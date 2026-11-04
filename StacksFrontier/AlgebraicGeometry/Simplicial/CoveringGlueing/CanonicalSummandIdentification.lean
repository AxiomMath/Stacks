module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.TransitionSections
public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.SummandTotalRestriction
public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.SliceRestrictionComparison
public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.CechLift
public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.LocallyGivenOfCovering
public import StacksFrontier.CategoryTheory.Localization.InducedNatTransSourceIso
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedTransitionInduced

/-!
# The restriction of an object of `D(O_X)` to the total site, on summands
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace SheafOfModules

/-- Restriction of sections of the abelian sheaf underlying a pushforward of modules along `g`
is restriction of sections of `N` along `F.map g`. -/
theorem moduleSheaf_pushforward_obj_map_apply {C' : Type*} [Category* C'] {D : Type*} [Category* D]
    {J : GrothendieckTopology C'} {K' : GrothendieckTopology D} (F : C' ⥤ D)
    [hF : F.IsContinuous J K'] {S : Sheaf J RingCat.{u}} {R : Sheaf K' RingCat.{u}}
    [hJ : J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
    [hK : K'.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K').obj R) (N : SheafOfModules.{u} R)
    {U V : C'ᵒᵖ} (g : U ⟶ V) (y) :
    (Sheaf.moduleSheaf S ((pushforward.{u} φ).obj N)).obj.map g y =
      (N.val.presheaf.map (F.map g.unop).op).hom y :=
  rfl

end SheafOfModules

namespace CategoryTheory.Functor

variable {A : Type*} [Category* A] [Preadditive A] {B : Type*} [Category* B] [Preadditive B]
  {B' : Type*} [Category* B'] [Preadditive B'] {D : Type*} [Category* D] [Preadditive D]
  {D' : Type*} [Category* D'] [Preadditive D'] {E : Type*} [Category* E] [Preadditive E]
  (F₁ : A ⥤ B) (F₂ : B ⥤ D) (F₃ : D ⥤ E) (G₁ : A ⥤ B') (G₂ : B' ⥤ D') (G₃ : D' ⥤ E)
  [hF₁ : F₁.Additive] [hF₂ : F₂.Additive] [hF₃ : F₃.Additive] [hG₁ : G₁.Additive]
  [hG₂ : G₂.Additive] [hG₃ : G₃.Additive] (θ : F₁ ⋙ F₂ ⋙ F₃ ≅ G₁ ⋙ G₂ ⋙ G₃) {ι' : Type*}
  (c : ComplexShape ι')

/-- An isomorphism of threefold composites of additive functors, acting on complexes. -/
def mapHomologicalComplexComp₃Iso :
    F₁.mapHomologicalComplex c ⋙ F₂.mapHomologicalComplex c ⋙ F₃.mapHomologicalComplex c ≅
      G₁.mapHomologicalComplex c ⋙ G₂.mapHomologicalComplex c ⋙ G₃.mapHomologicalComplex c :=
  NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun p => θ.app (K.X p))
    (fun p q _ => (θ.hom.naturality (K.d p q)).symm)) fun g => by
      ext p
      exact θ.hom.naturality (g.f p)

/-- The degree-`p` component of `mapHomologicalComplexComp₃Iso` is `θ` at `K.X p`. -/
@[simp]
theorem mapHomologicalComplexComp₃Iso_hom_app_f (K : HomologicalComplex A c) (p : ι') :
    ((mapHomologicalComplexComp₃Iso F₁ F₂ F₃ G₁ G₂ G₃ θ c).hom.app K).f p = θ.hom.app (K.X p) :=
  rfl

/-- The degree-`p` component of the inverse of `mapHomologicalComplexComp₃Iso` is the inverse
of `θ` at `K.X p`. -/
@[simp]
theorem mapHomologicalComplexComp₃Iso_inv_app_f (K : HomologicalComplex A c) (p : ι') :
    ((mapHomologicalComplexComp₃Iso F₁ F₂ F₃ G₁ G₂ G₃ θ c).inv.app K).f p = θ.inv.app (K.X p) :=
  rfl

section TransitionComponent

variable {A' : Type*} [Category* A'] [Preadditive A'] {B₁ : Type*} [Category* B₁] [Preadditive B₁]
  {Cm' : Type*} [Category* Cm'] [Preadditive Cm'] {Dn : Type*} [Category* Dn] [Preadditive Dn]
  {B₂ : Type*} [Category* B₂] [Preadditive B₂] {D₂ : Type*} [Category* D₂] [Preadditive D₂]
  {S' : Type*} [Category* S'] {J' : GrothendieckTopology S'} {Rg : Sheaf J' RingCat.{u}}
  (R : A' ⥤ B₁) (Cm : B₁ ⥤ Cm') (π τ : Cm' ⥤ Dn) (Cn : B₁ ⥤ Dn)
  (Sg : Dn ⥤ SheafOfModules.{u} Rg) (H₁ : A' ⥤ B₂) (H₂ : B₂ ⥤ D₂)
  (H₃ : D₂ ⥤ SheafOfModules.{u} Rg)
  [hR : R.Additive] [hCm : Cm.Additive] [hπ : π.Additive] [hτ : τ.Additive] [hCn : Cn.Additive]
  [hSg : Sg.Additive] [hH₁ : H₁.Additive] [hH₂ : H₂.Additive] [hH₃ : H₃.Additive]
  (tp : π ≅ τ) (t : Cm ⋙ π ⟶ Cn) (θ : R ⋙ Cn ⋙ Sg ≅ H₁ ⋙ H₂ ⋙ H₃)

/-- A transition of restrictions, read through an identification of pullback with restriction
and followed by a section-fixing identification, fixes sections degreewise as soon as it does on
objects. -/
theorem fixesSections_transitionComponent
    (h : ∀ M, SheafOfModules.FixesSections
      ((Sg.map (tp.inv.app (Cm.obj (R.obj M)) ≫ t.app (R.obj M))) ≫ θ.hom.app M))
    (K : CochainComplex A' ℤ) (p : ℤ) :
    SheafOfModules.FixesSections
      ((((Functor.isoWhiskerLeft (R.mapHomologicalComplex (ComplexShape.up ℤ))
          (Functor.isoWhiskerRight (Functor.isoWhiskerLeft
            (Cm.mapHomologicalComplex (ComplexShape.up ℤ))
            (NatIso.mapHomologicalComplex tp (ComplexShape.up ℤ)))
            (Sg.mapHomologicalComplex (ComplexShape.up ℤ)))).inv ≫
        Functor.whiskerLeft (R.mapHomologicalComplex (ComplexShape.up ℤ))
          (Functor.whiskerRight
            (NatTrans.mapHomologicalComplex t (ComplexShape.up ℤ))
            (Sg.mapHomologicalComplex (ComplexShape.up ℤ))) ≫
        (mapHomologicalComplexComp₃Iso R Cn Sg H₁ H₂ H₃ θ
          (ComplexShape.up ℤ)).hom).app K).f p) := by
  have e : (((Functor.isoWhiskerLeft (R.mapHomologicalComplex (ComplexShape.up ℤ))
          (Functor.isoWhiskerRight (Functor.isoWhiskerLeft
            (Cm.mapHomologicalComplex (ComplexShape.up ℤ))
            (NatIso.mapHomologicalComplex tp (ComplexShape.up ℤ)))
            (Sg.mapHomologicalComplex (ComplexShape.up ℤ)))).inv ≫
        Functor.whiskerLeft (R.mapHomologicalComplex (ComplexShape.up ℤ))
          (Functor.whiskerRight
            (NatTrans.mapHomologicalComplex t (ComplexShape.up ℤ))
            (Sg.mapHomologicalComplex (ComplexShape.up ℤ))) ≫
        (mapHomologicalComplexComp₃Iso R Cn Sg H₁ H₂ H₃ θ (ComplexShape.up ℤ)).hom).app K).f p =
      (Sg.map (tp.inv.app (Cm.obj (R.obj (K.X p)))) ≫ Sg.map (t.app (R.obj (K.X p)))) ≫
        θ.hom.app (K.X p) := by
    simp
  rw [e, ← Sg.map_comp]
  exact h (K.X p)

end TransitionComponent

section PullbackComponent

variable {A' : Type*} [Category* A'] [Preadditive A'] {B₁ : Type*} [Category* B₁] [Preadditive B₁]
  {Cm' : Type*} [Category* Cm'] [Preadditive Cm'] {Dn : Type*} [Category* Dn] [Preadditive Dn]
  {B₂ : Type*} [Category* B₂] [Preadditive B₂] {D₂ : Type*} [Category* D₂] [Preadditive D₂]
  {S' : Type*} [Category* S'] {J' : GrothendieckTopology S'} {Rg : Sheaf J' RingCat.{u}}
  {S'' : Type*} [Category* S''] {J'' : GrothendieckTopology S''} {Rs : Sheaf J'' RingCat.{u}}
  {T' : Type*} [Category* T'] [Preadditive T']
  (R : A' ⥤ B₁) (Cm : B₁ ⥤ Cm') (π τ : Cm' ⥤ Dn) (Sgt : Dn ⥤ SheafOfModules.{u} Rg)
  (Sgs : Cm' ⥤ SheafOfModules.{u} Rs) (r : SheafOfModules.{u} Rs ⥤ SheafOfModules.{u} Rg)
  (H₁ : A' ⥤ B₂) (H₂ : B₂ ⥤ D₂) (H₃ : D₂ ⥤ SheafOfModules.{u} Rs)
  [hR : R.Additive] [hCm : Cm.Additive] [hπ : π.Additive] [hτ : τ.Additive] [hSgt : Sgt.Additive]
  [hSgs : Sgs.Additive] [hr : r.Additive] [hH₁ : H₁.Additive] [hH₂ : H₂.Additive]
  [hH₃ : H₃.Additive]
  (tp : π ≅ τ) (sT : τ ⋙ Sgt ≅ Sgs ⋙ r) (θ : R ⋙ Cm ⋙ Sgs ≅ H₁ ⋙ H₂ ⋙ H₃)
  {T₀ : CochainComplex A' ℤ ⥤ CochainComplex (SheafOfModules.{u} Rg) ℤ}
  (γr : (H₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      H₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      H₃.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
      r.mapHomologicalComplex (ComplexShape.up ℤ) ⟶ T₀)

/-- The identification of degreewise pullback, then restriction, with restriction, then
restriction, acting on complexes. -/
def pullbackComponentComplexesIso :
    π.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Sgt.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      Sgs.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ r.mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.mapHomologicalComplex (Functor.isoWhiskerRight tp Sgt ≪≫ sT) (ComplexShape.up ℤ)

/-- A pullback of restrictions, read through an identification of pullback with restriction,
followed by a section-fixing identification and a section-fixing transformation, fixes sections
degreewise as soon as the pieces do. -/
theorem fixesSections_pullbackComponent
    (h : ∀ M, SheafOfModules.FixesSections (sT.hom.app (Cm.obj (R.obj M)) ≫ r.map (θ.hom.app M)))
    (hγr : ∀ K p, SheafOfModules.FixesSections ((γr.app K).f p))
    (K : CochainComplex A' ℤ) (p : ℤ) :
    SheafOfModules.FixesSections
      ((((Functor.isoWhiskerLeft (R.mapHomologicalComplex (ComplexShape.up ℤ))
          (Functor.isoWhiskerRight (Functor.isoWhiskerLeft
            (Cm.mapHomologicalComplex (ComplexShape.up ℤ))
            (NatIso.mapHomologicalComplex tp (ComplexShape.up ℤ)))
            (Sgt.mapHomologicalComplex (ComplexShape.up ℤ)))).inv ≫
        Functor.whiskerLeft (R.mapHomologicalComplex (ComplexShape.up ℤ))
          (Functor.associator _ _ _).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerLeft _ (pullbackComponentComplexesIso π τ Sgt Sgs r tp sT).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Functor.associator _ _ _).hom _ ≫
        Functor.whiskerRight (mapHomologicalComplexComp₃Iso R Cm Sgs H₁ H₂ H₃ θ
          (ComplexShape.up ℤ)).hom _ ≫ γr).app K).f p) := by
  have e : ((((Functor.isoWhiskerLeft (R.mapHomologicalComplex (ComplexShape.up ℤ))
          (Functor.isoWhiskerRight (Functor.isoWhiskerLeft
            (Cm.mapHomologicalComplex (ComplexShape.up ℤ))
            (NatIso.mapHomologicalComplex tp (ComplexShape.up ℤ)))
            (Sgt.mapHomologicalComplex (ComplexShape.up ℤ)))).inv ≫
        Functor.whiskerLeft (R.mapHomologicalComplex (ComplexShape.up ℤ))
          (Functor.associator _ _ _).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerLeft _ (pullbackComponentComplexesIso π τ Sgt Sgs r tp sT).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Functor.associator _ _ _).hom _ ≫
        Functor.whiskerRight (mapHomologicalComplexComp₃Iso R Cm Sgs H₁ H₂ H₃ θ
          (ComplexShape.up ℤ)).hom _ ≫ γr).app K).f p) =
      (sT.hom.app (Cm.obj (R.obj (K.X p))) ≫ r.map (θ.hom.app (K.X p))) ≫ (γr.app K).f p := by
    simp [pullbackComponentComplexesIso, ← Sgt.map_comp_assoc]
  rw [e]
  exact (h (K.X p)).comp (hγr K p)

end PullbackComponent

end CategoryTheory.Functor

namespace CategoryTheory.SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))
  (OC : Sheaf P.toGrothendieck CommRingCat.{u})

attribute [local instance] pretopologyRingedSite_over_hasPullbacks

/-- Restriction of sections of the restriction to the total site of a sheaf of `O_X`-modules,
along an arrow of the total site lying over an identity, is the identity on sections. -/
theorem moduleSheaf_totalRestrictionModules_map_heq
    [hsc : (situation ((pretopologyRingedSite P OC).over X).J K).totalTopology.HasSheafCompose
      (CategoryTheory.forget AddCommGrpCat.{u})]
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (OC.over X)))
    {a b : Grothendieck (slices K)} (g : a ⟶ b)
    (hab : (totalForget K).obj a = (totalForget K).obj b)
    (hg : (totalForget K).map g = eqToHom hab) (y) :
    HEq ((Sheaf.moduleSheaf.{u, u, u}
      ((situation ((pretopologyRingedSite P OC).over X).J K).totalRingSheaf
        (structureSheaf ((pretopologyRingedSite P OC).over X) K))
      ((totalRestrictionModules P K OC).obj N)).obj.map g.op y) y := by
  refine HEq.trans (heq_of_eq (SheafOfModules.moduleSheaf_pushforward_obj_map_apply (totalForget K)
    (hF := by exact totalForget_isContinuous _ K) (hJ := hsc) _ N g.op y)) ?_
  rw [Quiver.Hom.unop_op, hg, eqToHom_op]
  exact SheafOfModules.heq_presheaf_map_eqToHom N.val.presheaf _ y

/-- **The transitions of the restriction of a sheaf of `O_X`-modules to the total site are the
identity on sections.** -/
theorem transitionOfRestriction_totalRestrictionModules_fixesSections {m n : SimplexCategory}
    (φ : m ⟶ n) (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (OC.over X))) :
    SheafOfModules.FixesSections (transitionOfRestriction ((pretopologyRingedSite P OC).over X) K φ
      ((totalRestrictionModules P K OC).obj N)) := by
  intro V y
  have h := moduleSheafFunctor_map_transitionOfRestriction_app_apply
    ((pretopologyRingedSite P OC).over X) K φ ((totalRestrictionModules P K OC).obj N) V.unop y
  refine HEq.trans (heq_of_eq h) ?_
  exact moduleSheaf_totalRestrictionModules_map_heq P K OC (hsc := _) N
    ((Grothendieck.ιNatTrans (F := slices K) φ.op).app (V.unop : ((slices K).obj (op n) : Cat)))
    rfl ((totalForget_map_ιNatTrans_app K φ.op _).trans (eqToHom_refl _ _).symm) y

end CategoryTheory.SimplicialSemiRepresentable

namespace AlgebraicGeometry.RingedSite.CoveringGlueing

open CategoryTheory.SimplicialSemiRepresentable

attribute [local instance] HasDerivedCategory.standard pretopologyRingedSite_over_hasPullbacks

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (OC : Sheaf P.toGrothendieck CommRingCat.{u}) {ι : Type u} {U : ι → C} (f : ∀ i, U i ⟶ X)

/-- The slice `C/X` of a category with fibre products has finite products. -/
instance hasFiniteProducts_over : HasFiniteProducts (Over X) :=
  letI : HasTerminal (Over X) := Over.over_hasTerminal X
  letI : HasBinaryProducts (Over X) := Over.ConstructProducts.over_binaryProduct_of_pullback
  hasFiniteProducts_of_has_binary_and_terminal

/-- The localized ringed site `C/X`, with its universes made explicit. -/
abbrev overRingedSite : RingedSite.{u, u, u} := (pretopologyRingedSite P OC).over X

/-- The coverage of the localized ringed site `C/X` has pullbacks. -/
instance overRingedSite_hasPullbacks : (overRingedSite P OC (X := X)).J.toCoverage.HasPullbacks :=
  pretopologyRingedSite_over_hasPullbacks P OC

/-- The Čech object of the family, as a simplicial object of `SR(C/X)`. -/
abbrev cechObject : SimplicialObject (FormalCoproduct.{u} (Over X)) :=
  (family (X := pretopologyRingedSite P OC) f).cech

/-- The index attached to the summand `t` of the degree-`n` term of the Čech object. -/
abbrev cechIdx (n : SimplexCategory) (t : ((cechObject P OC f).obj (op n)).I) :
    Index (X := pretopologyRingedSite P OC) f :=
  cechIndex (X := pretopologyRingedSite P OC) f (op n) t

/-- On sheaves of modules: restricting an `O_X`-module to the total site, then to the summand
`t` of the degree-`n` term of the Čech object, is restricting it along the arrow to `U_{t_0}` and
transporting it to the iterated slice. -/
def canonicalSummandModulesIso (n : SimplexCategory) (t : ((cechObject P OC f).obj (op n)).I) :
    totalRestrictionModules P (cechObject P OC f) OC ⋙
        (situation (P.toGrothendieck.over X) (cechObject P OC f)).componentModulesRestriction
          (structureSheafAugmentation P (cechObject P OC f) OC).O n ⋙
        summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n t ≅
      (pretopologyRingedSite P OC).overMapModules (f (cechIdx P OC f n t).i) ⋙
        (pretopologyRingedSite P OC).overMapModules (cechIdx P OC f n t).a ⋙
          (pretopologyRingedSite P OC).iteratedSliceTransport X (cechIdx P OC f n t).V :=
  summandTotalRestrictionIso P (cechObject P OC f) OC n t ≪≫
    ((pretopologyRingedSite P OC).sliceRestrictionOverMapModulesIso (cechIdx P OC f n t).V
      (cechIdx P OC f n t).a (f (cechIdx P OC f n t).i) (cechIdx P OC f n t).w).symm

/-- Restriction to the summand `t` of the degree-`n` term of the Čech object is additive. -/
instance cech_summandRestriction_additive (n : SimplexCategory)
    (t : ((cechObject P OC f).obj (op n)).I) :
    (summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n t).Additive :=
  summandRestriction_additive (overRingedSite P OC (X := X)) (cechObject P OC f) n t

/-- Restriction to the summand `t` of the degree-`n` term of the Čech object preserves finite
limits. -/
instance cech_summandRestriction_preservesFiniteLimits (n : SimplexCategory)
    (t : ((cechObject P OC f).obj (op n)).I) :
    PreservesFiniteLimits
      (summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n t) :=
  summandRestriction_preservesFiniteLimits (overRingedSite P OC (X := X)) (cechObject P OC f) n t

/-- Restriction to the summand `t` of the degree-`n` term of the Čech object preserves finite
colimits. -/
instance cech_summandRestriction_preservesFiniteColimits (n : SimplexCategory)
    (t : ((cechObject P OC f).obj (op n)).I) :
    PreservesFiniteColimits
      (summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n t) :=
  summandRestriction_preservesFiniteColimits (overRingedSite P OC (X := X)) (cechObject P OC f) n t

/-- The factorization through complexes of restricting an object of `D(O_X)` to the total site,
then to the degree-`n` component, then to its summand `t`. -/
abbrev canonicalSummandSourceFactors (n : SimplexCategory)
    (t : ((cechObject P OC f).obj (op n)).I) :=
  Functor.compFactorization
    (totalRestrictionModules P (cechObject P OC f) OC).mapDerivedCategoryFactors
    (Functor.compFactorization
      ((situation (P.toGrothendieck.over X) (cechObject P OC f)).componentModulesRestriction
        (structureSheafAugmentation P (cechObject P OC f) OC).O n).mapDerivedCategoryFactors
      (summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n
        t).mapDerivedCategoryFactors)

/-- The factorization through complexes of restricting an object of `D(O_X)` along the arrow to
`U_{t_0}`, then along `a`, and transporting it to the iterated slice. -/
abbrev canonicalSummandTargetFactors (n : SimplexCategory)
    (t : ((cechObject P OC f).obj (op n)).I) :=
  Functor.compFactorization
    ((pretopologyRingedSite P OC).derivedOverMapFactors (f (cechIdx P OC f n t).i))
    (Functor.compFactorization
      ((pretopologyRingedSite P OC).derivedOverMapFactors (cechIdx P OC f n t).a)
      ((pretopologyRingedSite P OC).derivedIteratedSliceTransportFactors X (cechIdx P OC f n t).V))

/-- **The canonical identification of the summands of the restriction of an object of `D(O_X)`
to the total site of the Čech object.** -/
def canonicalSummandIso (n : SimplexCategory) (t : ((cechObject P OC f).obj (op n)).I) :=
  NatIso.liftAlong (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (canonicalSummandSourceFactors P OC f n t) (canonicalSummandTargetFactors P OC f n t)
    (Functor.mapHomologicalComplexComp₃Iso _ _ _ _ _ _ (canonicalSummandModulesIso P OC f n t)
      (hF₁ := totalRestrictionModules_additive P (cechObject P OC f) OC)
      (hF₂ := SimplicialSiteSituation.componentModulesRestriction_additive _ _ n)
      (hF₃ := cech_summandRestriction_additive P OC f n t)
      (hG₁ := RingedSite.overMapModules_additive _ _)
      (hG₂ := RingedSite.overMapModules_additive _ _)
      (hG₃ := RingedSite.iteratedSliceTransport_additive _ _ _) (ComplexShape.up ℤ))

/-- The canonical identification of summands is induced by the canonical identification of
complexes of sheaves of modules. -/
theorem canonicalSummandIso_hom_isInducedBy (n : SimplexCategory)
    (t : ((cechObject P OC f).obj (op n)).I) :
    NatTrans.IsInducedBy (canonicalSummandSourceFactors P OC f n t)
      (canonicalSummandTargetFactors P OC f n t) (canonicalSummandIso P OC f n t).hom
      (Functor.mapHomologicalComplexComp₃Iso _ _ _ _ _ _ (canonicalSummandModulesIso P OC f n t)
        (hF₁ := totalRestrictionModules_additive P (cechObject P OC f) OC)
        (hF₂ := SimplicialSiteSituation.componentModulesRestriction_additive _ _ n)
        (hF₃ := cech_summandRestriction_additive P OC f n t)
        (hG₁ := RingedSite.overMapModules_additive _ _)
        (hG₂ := RingedSite.overMapModules_additive _ _)
        (hG₃ := RingedSite.iteratedSliceTransport_additive _ _ _) (ComplexShape.up ℤ)).hom :=
  NatTrans.isInducedBy_liftAlong _ _ _ _

/-- The canonical identification of complexes fixes sections in every degree. -/
theorem canonicalSummandModulesIso_hom_app_fixesSections (n : SimplexCategory)
    (t : ((cechObject P OC f).obj (op n)).I)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (OC.over X))) :
    SheafOfModules.FixesSections ((canonicalSummandModulesIso P OC f n t).hom.app N) :=
  (summandTotalRestrictionIso_hom_app_fixesSections P (cechObject P OC f) OC n t N).comp
    ((pretopologyRingedSite P OC).sliceRestrictionOverMapModulesIso_inv_app_fixesSections _ _ _ _ N)

/-- **The data of Situation 0DC9 attached to a global object** `N` of `D(O_X)`: the restrictions
`N|_{U_i}` glued by the canonical comparisons on the overlaps. -/
def globalLocallyGiven (N : LocalDerivedCategory.{0} (pretopologyRingedSite P OC) X) :
    LocallyGiven.{0, u, u, u, u, u} (overRingedSite P OC (X := X)) :=
  locallyGiven (X := pretopologyRingedSite P OC) f
    (fun i => (derivedOverMap.{0} (pretopologyRingedSite P OC) (f i)).obj N)
    (canonicalOverlap (X := pretopologyRingedSite P OC) f N)
    (isCocycle_canonicalOverlap (X := pretopologyRingedSite P OC) f N)

/-- The transitions of the total site of the Čech object are flat. -/
theorem cech_transitionRingedToposHom_isFlat {m n : SimplexCategory} (φ : m ⟶ n) :
    ((situation (P.toGrothendieck.over X) (cechObject P OC f)).transitionRingedToposHom
      (structureSheafAugmentation P (cechObject P OC f) OC).O φ).IsFlat :=
  transitionRingedToposHom_isFlat (overRingedSite P OC (X := X)) (cechObject P OC f) φ

/-- The derived transition of the restriction of an object of `D(O_X)` to the total site, read on
the summand `t`, followed by the canonical identification of that summand, is induced
degreewise. -/
theorem canonicalSummand_transition_isInducedBy {m n : SimplexCategory} (φ : m ⟶ n)
    (t : ((cechObject P OC f).obj (op n)).I) :
    letI := (situation (P.toGrothendieck.over X)
      (cechObject P OC f)).transitionPullbackModules_preservesFiniteLimits
      (structureSheafAugmentation P (cechObject P OC f) OC).O φ
      (cech_transitionRingedToposHom_isFlat P OC f φ)
    NatTrans.IsInducedBy
      (Functor.compFactorization
        (totalRestrictionModules P (cechObject P OC f) OC).mapDerivedCategoryFactors
        (Functor.compFactorization
          (Functor.compFactorization
            ((situation (P.toGrothendieck.over X) (cechObject P OC f)).componentModulesRestriction
              (structureSheafAugmentation P (cechObject P OC f) OC).O m).mapDerivedCategoryFactors
            ((situation (P.toGrothendieck.over X)
              (cechObject P OC f)).derivedTransitionPullbackFactors
              (structureSheafAugmentation P (cechObject P OC f) OC).O φ
              (cech_transitionRingedToposHom_isFlat P OC f φ)))
          (summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n
            t).mapDerivedCategoryFactors))
      (canonicalSummandTargetFactors P OC f n t)
      (Functor.whiskerLeft (totalRestrictionModules P (cechObject P OC f) OC).mapDerivedCategory
          (Functor.whiskerRight
            ((situation (P.toGrothendieck.over X)
              (cechObject P OC f)).derivedComponentModuleTransition
              (structureSheafAugmentation P (cechObject P OC f) OC).O φ)
            (summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n
              t).mapDerivedCategory) ≫
        (canonicalSummandIso P OC f n t).hom)
      (Functor.whiskerLeft ((totalRestrictionModules P (cechObject P OC f) OC).mapHomologicalComplex
          (ComplexShape.up ℤ))
          (Functor.whiskerRight
            (NatTrans.mapHomologicalComplex
              ((situation (P.toGrothendieck.over X) (cechObject P OC f)).componentModulesTransition
                (structureSheafAugmentation P (cechObject P OC f) OC).O φ) (ComplexShape.up ℤ))
            ((summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n
              t).mapHomologicalComplex (ComplexShape.up ℤ))) ≫
        (Functor.mapHomologicalComplexComp₃Iso _ _ _ _ _ _ (canonicalSummandModulesIso P OC f n t)
          (hF₁ := totalRestrictionModules_additive P (cechObject P OC f) OC)
          (hF₂ := SimplicialSiteSituation.componentModulesRestriction_additive _ _ n)
          (hF₃ := cech_summandRestriction_additive P OC f n t)
          (hG₁ := RingedSite.overMapModules_additive _ _)
          (hG₂ := RingedSite.overMapModules_additive _ _)
          (hG₃ := RingedSite.iteratedSliceTransport_additive _ _ _) (ComplexShape.up ℤ)).hom) :=
  (NatTrans.IsInducedBy.whiskerLeft _
    (((situation (P.toGrothendieck.over X)
      (cechObject P OC f)).derivedComponentModuleTransition_isInducedBy
      (structureSheafAugmentation P (cechObject P OC f) OC).O φ
      (cech_transitionRingedToposHom_isFlat P OC f φ)).whiskerRight _)).comp
    (canonicalSummandIso_hom_isInducedBy P OC f n t)

/-- **The isomorphisms `ρ_g` of the locally given datum of a global object, as natural
transformations in the global object**, for an arrow `g : b' ⟶ b` of the indexing category. -/
def globalRhoNat {b b' : IndexCategory (X := pretopologyRingedSite P OC) f} (g : b' ⟶ b) :
    (derivedOverMap.{0} (pretopologyRingedSite P OC) (f b.i) ⋙
        derivedOverMap.{0} (pretopologyRingedSite P OC) b.a ⋙
          (pretopologyRingedSite P OC).derivedIteratedSliceTransport X b.V) ⋙
        derivedOverMap.{0} ((pretopologyRingedSite P OC).over X) g.hom ⟶
      derivedOverMap.{0} (pretopologyRingedSite P OC) (f b'.i) ⋙
        derivedOverMap.{0} (pretopologyRingedSite P OC) b'.a ⋙
          (pretopologyRingedSite P OC).derivedIteratedSliceTransport X b'.V :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (Functor.whiskerLeft _
      ((pretopologyRingedSite P OC).derivedIteratedSliceTransportOverMapIso X g.hom).hom) ≫
    Functor.whiskerLeft _ (Functor.associator _ _ _).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (canonicalRestrictionComparison (X := pretopologyRingedSite P OC) f b.a
      g.hom.left b'.a (Index.comp_w g)) _ ≫
    (Functor.associator _ _ _).hom

/-- The component of `globalRhoNat` at a global object `N` is the isomorphism `ρ_g` of the
locally given datum attached to `N`. -/
theorem globalRhoNat_app {b b' : IndexCategory (X := pretopologyRingedSite P OC) f} (g : b' ⟶ b)
    (N : LocalDerivedCategory.{0} (pretopologyRingedSite P OC) X) :
    (globalRhoNat P OC f g).app N = ((globalLocallyGiven P OC f N).rho g).hom := by
  simp only [globalRhoNat, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    canonicalRestrictionComparison_app]
  refine (Category.id_comp _).trans (Eq.trans (congrArg (fun t => _ ≫ t)
    ((Category.id_comp _).trans (Category.comp_id _))) ?_)
  rfl

/-- The natural isomorphisms `ρ_g` of the locally given datum of a global object are induced by
transformations of complexes fixing sections. -/
theorem globalRhoNat_isInducedBy {b b' : IndexCategory (X := pretopologyRingedSite P OC) f}
    (g : b' ⟶ b) :
    ∃ γ₀, NatTrans.IsInducedBy
      (Functor.compFactorization
        (Functor.compFactorization
          ((pretopologyRingedSite P OC).derivedOverMapFactors (f b.i))
          (Functor.compFactorization ((pretopologyRingedSite P OC).derivedOverMapFactors b.a)
            ((pretopologyRingedSite P OC).derivedIteratedSliceTransportFactors X b.V)))
        (((pretopologyRingedSite P OC).over X).derivedOverMapFactors g.hom))
      (Functor.compFactorization
        ((pretopologyRingedSite P OC).derivedOverMapFactors (f b'.i))
        (Functor.compFactorization ((pretopologyRingedSite P OC).derivedOverMapFactors b'.a)
          ((pretopologyRingedSite P OC).derivedIteratedSliceTransportFactors X b'.V)))
      (globalRhoNat P OC f g) γ₀ ∧
      ∀ K p, SheafOfModules.FixesSections ((γ₀.app K).f p) := by
  have h1 := NatTrans.IsInducedBy.associator
    ((pretopologyRingedSite P OC).derivedOverMapFactors (f b.i))
    (Functor.compFactorization ((pretopologyRingedSite P OC).derivedOverMapFactors b.a)
      ((pretopologyRingedSite P OC).derivedIteratedSliceTransportFactors X b.V))
    (((pretopologyRingedSite P OC).over X).derivedOverMapFactors g.hom)
  have h2 := NatTrans.IsInducedBy.whiskerLeft
    ((pretopologyRingedSite P OC).derivedOverMapFactors (f b.i))
    (NatTrans.IsInducedBy.associator ((pretopologyRingedSite P OC).derivedOverMapFactors b.a)
      ((pretopologyRingedSite P OC).derivedIteratedSliceTransportFactors X b.V)
      (((pretopologyRingedSite P OC).over X).derivedOverMapFactors g.hom))
  have h3 := NatTrans.IsInducedBy.whiskerLeft
    ((pretopologyRingedSite P OC).derivedOverMapFactors (f b.i))
    (NatTrans.IsInducedBy.whiskerLeft ((pretopologyRingedSite P OC).derivedOverMapFactors b.a)
      ((pretopologyRingedSite P OC).derivedIteratedSliceTransportOverMapIso_hom_isInducedBy X
        g.hom))
  have h4 := NatTrans.IsInducedBy.whiskerLeft
    ((pretopologyRingedSite P OC).derivedOverMapFactors (f b.i))
    (NatTrans.IsInducedBy.associator_inv ((pretopologyRingedSite P OC).derivedOverMapFactors b.a)
      ((pretopologyRingedSite P OC).derivedOverMapFactors g.hom.left)
      ((pretopologyRingedSite P OC).derivedIteratedSliceTransportFactors X b'.V))
  have h5 := NatTrans.IsInducedBy.associator_inv
    ((pretopologyRingedSite P OC).derivedOverMapFactors (f b.i))
    (Functor.compFactorization ((pretopologyRingedSite P OC).derivedOverMapFactors b.a)
      ((pretopologyRingedSite P OC).derivedOverMapFactors g.hom.left))
    ((pretopologyRingedSite P OC).derivedIteratedSliceTransportFactors X b'.V)
  have h6 := (canonicalRestrictionComparison_isInducedBy (X := pretopologyRingedSite P OC) f b.a
    g.hom.left b'.a (Index.comp_w g)).whiskerRight
      ((pretopologyRingedSite P OC).derivedIteratedSliceTransportFactors X b'.V)
  have h7 := NatTrans.IsInducedBy.associator
    ((pretopologyRingedSite P OC).derivedOverMapFactors (f b'.i))
    ((pretopologyRingedSite P OC).derivedOverMapFactors b'.a)
    ((pretopologyRingedSite P OC).derivedIteratedSliceTransportFactors X b'.V)
  refine ⟨_, h1.comp (h2.comp (h3.comp (h4.comp (h5.comp (h6.comp h7))))), fun K p => ?_⟩
  simp_fixesSections
  fixes_sections

/-- Restriction along a relocalization functor is additive. -/
instance cech_transitionRestriction_additive {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) φ).Additive where
  map_add := rfl

/-- On complexes: degreewise pullback along `f_φ` is degreewise restriction along `r_φ`, after
restriction to the total site and to the degree-`m` component, and before restriction to the
summand `t`. -/
abbrev cechSourceComplexIso {m n : SimplexCategory} (φ : m ⟶ n)
    (t : ((cechObject P OC f).obj (op n)).I) :=
  Functor.isoWhiskerLeft ((totalRestrictionModules P (cechObject P OC f) OC).mapHomologicalComplex
      (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight (Functor.isoWhiskerLeft
      (((situation (P.toGrothendieck.over X) (cechObject P OC f)).componentModulesRestriction
        (structureSheafAugmentation P (cechObject P OC f) OC).O m).mapHomologicalComplex
          (ComplexShape.up ℤ))
      (NatIso.mapHomologicalComplex
        (transitionPullbackModulesIso (overRingedSite P OC (X := X)) (cechObject P OC f) φ)
        (ComplexShape.up ℤ)))
      ((summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n
        t).mapHomologicalComplex (ComplexShape.up ℤ)))

/-- The source factorization of the transition side, read through restriction along `r_φ`. -/
abbrev cechTransitionSourceFactors {m n : SimplexCategory} (φ : m ⟶ n)
    (t : ((cechObject P OC f).obj (op n)).I) :=
  letI := (situation (P.toGrothendieck.over X)
    (cechObject P OC f)).transitionPullbackModules_preservesFiniteLimits
      (structureSheafAugmentation P (cechObject P OC f) OC).O φ
      (cech_transitionRingedToposHom_isFlat P OC f φ)
  Functor.compFactorization
    (totalRestrictionModules P (cechObject P OC f) OC).mapDerivedCategoryFactors
      (Functor.compFactorization
        (Functor.compFactorization
          ((situation (P.toGrothendieck.over X) (cechObject P OC f)).componentModulesRestriction
            (structureSheafAugmentation P (cechObject P OC f) OC).O m).mapDerivedCategoryFactors
          ((situation (P.toGrothendieck.over X)
            (cechObject P OC f)).derivedTransitionPullbackFactors
            (structureSheafAugmentation P (cechObject P OC f) OC).O φ
            (cech_transitionRingedToposHom_isFlat P OC f φ)))
        (summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n
          t).mapDerivedCategoryFactors) ≪≫
    Functor.isoWhiskerRight (cechSourceComplexIso P OC f φ t) DerivedCategory.Q

/-- The transition side of the compatibility of the canonical identification of summands. -/
abbrev cechTransitionNat {m n : SimplexCategory} (φ : m ⟶ n)
    (t : ((cechObject P OC f).obj (op n)).I) :=
  Functor.whiskerLeft (totalRestrictionModules P (cechObject P OC f) OC).mapDerivedCategory
      (Functor.whiskerRight
        ((situation (P.toGrothendieck.over X) (cechObject P OC f)).derivedComponentModuleTransition
          (structureSheafAugmentation P (cechObject P OC f) OC).O φ)
        (summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n
          t).mapDerivedCategory) ≫
    (canonicalSummandIso P OC f n t).hom

/-- Restriction of sheaves of `O_X`-modules to the total site of the Čech object, with its target
spelled as the modules of the total ringed site of `C/X` and the Čech object. -/
abbrev cechTotalRestriction :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (overRingedSite P OC (X := X)).O) ⥤
      ((situation (overRingedSite P OC (X := X)).J (cechObject P OC f)).totalRingedTopos
        (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f))).Modules :=
  totalRestrictionModules P (cechObject P OC f) OC

/-- Restriction to the total site of the Čech object is additive. -/
instance cechTotalRestriction_additive : (cechTotalRestriction P OC f).Additive :=
  totalRestrictionModules_additive P (cechObject P OC f) OC

/-- Restriction to the total site of the Čech object preserves finite limits. -/
instance cechTotalRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (cechTotalRestriction P OC f) :=
  totalRestrictionModules_preservesFiniteLimits P (cechObject P OC f) OC

/-- Restriction to the total site of the Čech object preserves finite colimits. -/
instance cechTotalRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (cechTotalRestriction P OC f) :=
  totalRestrictionModules_preservesFiniteColimits P (cechObject P OC f) OC

/-- `canonicalSummandModulesIso` in the spelling of 0DCA. -/
def cechSummandModulesIso (n : SimplexCategory) (t : ((cechObject P OC f).obj (op n)).I) :
    cechTotalRestriction P OC f ⋙
        (situation (overRingedSite P OC (X := X)).J (cechObject P OC f)).componentModulesRestriction
          (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f)) n ⋙
        summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n t ≅
      (pretopologyRingedSite P OC).overMapModules (f (cechIdx P OC f n t).i) ⋙
        (pretopologyRingedSite P OC).overMapModules (cechIdx P OC f n t).a ⋙
          (pretopologyRingedSite P OC).iteratedSliceTransport X (cechIdx P OC f n t).V :=
  canonicalSummandModulesIso P OC f n t

/-- The section-fixing identification of complexes underlying `cechSummandIso`. -/
abbrev cechSummandComplexIso (n : SimplexCategory) (t : ((cechObject P OC f).obj (op n)).I) :=
  Functor.mapHomologicalComplexComp₃Iso _ _ _ _ _ _ (cechSummandModulesIso P OC f n t)
    (hF₁ := cechTotalRestriction_additive P OC f)
    (hF₂ := SimplicialSiteSituation.componentModulesRestriction_additive _ _ n)
    (hF₃ := cech_summandRestriction_additive P OC f n t)
    (hG₁ := RingedSite.overMapModules_additive _ _)
    (hG₂ := RingedSite.overMapModules_additive _ _)
    (hG₃ := RingedSite.iteratedSliceTransport_additive _ _ _) (ComplexShape.up ℤ)

/-- The source factorization of `cechSummandIso`. -/
abbrev cechSummandSourceFactors (n : SimplexCategory) (t : ((cechObject P OC f).obj (op n)).I) :=
  Functor.compFactorization (cechTotalRestriction P OC f).mapDerivedCategoryFactors
    (Functor.compFactorization
      ((situation (overRingedSite P OC (X := X)).J (cechObject P OC f)).componentModulesRestriction
        (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f))
          n).mapDerivedCategoryFactors
      (summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n
        t).mapDerivedCategoryFactors)

/-- **The canonical identification of the summands of the restriction of an object of `D(O_X)`
to the total site of the Čech object**, in the spelling of 0DCA. -/
def cechSummandIso (n : SimplexCategory) (t : ((cechObject P OC f).obj (op n)).I) :=
  NatIso.liftAlong (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (cechSummandSourceFactors P OC f n t) (canonicalSummandTargetFactors P OC f n t)
    (cechSummandComplexIso P OC f n t)

/-- The isomorphism `cechSummandIso` is induced by the identification of complexes
`cechSummandComplexIso`. -/
theorem cechSummandIso_hom_isInducedBy (n : SimplexCategory)
    (t : ((cechObject P OC f).obj (op n)).I) :
    NatTrans.IsInducedBy (cechSummandSourceFactors P OC f n t)
      (canonicalSummandTargetFactors P OC f n t) (cechSummandIso P OC f n t).hom
      (cechSummandComplexIso P OC f n t).hom :=
  NatTrans.isInducedBy_liftAlong _ _ _ _

/-- Restriction of sections of the restriction to the total site of the Čech object, along an
arrow lying over an identity, is the identity on sections; in the spelling of 0DCA. -/
theorem cech_moduleSheaf_map_heq
    [hsc : (situation (overRingedSite P OC (X := X)).J
      (cechObject P OC f)).totalTopology.HasSheafCompose
      (CategoryTheory.forget AddCommGrpCat.{u})]
    (N : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (overRingedSite P OC (X := X)).O))
    {a b : Grothendieck (slices (cechObject P OC f))} (g : a ⟶ b)
    (hab : (totalForget (cechObject P OC f)).obj a = (totalForget (cechObject P OC f)).obj b)
    (hg : (totalForget (cechObject P OC f)).map g = eqToHom hab) (y) :
    HEq ((Sheaf.moduleSheaf.{u, u, u}
      ((situation (overRingedSite P OC (X := X)).J (cechObject P OC f)).totalRingSheaf
        (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f)))
      ((cechTotalRestriction P OC f).obj N)).obj.map g.op y) y := by
  refine HEq.trans (heq_of_eq (SheafOfModules.moduleSheaf_pushforward_obj_map_apply
    (totalForget (cechObject P OC f))
    (hF := by exact totalForget_isContinuous _ (cechObject P OC f)) (hJ := hsc) _ N g.op y)) ?_
  rw [Quiver.Hom.unop_op, hg, eqToHom_op]
  exact SheafOfModules.heq_presheaf_map_eqToHom N.val.presheaf _ y

/-- The module transitions of the restriction of a sheaf of `O_X`-modules to the total site of
the Čech object fix sections, in the spelling of 0DCA. -/
theorem cech_transitionOfRestriction_fixesSections {m n : SimplexCategory} (φ : m ⟶ n)
    (N : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (overRingedSite P OC (X := X)).O)) :
    SheafOfModules.FixesSections (transitionOfRestriction (overRingedSite P OC (X := X))
      (cechObject P OC f) φ
      ((cechTotalRestriction P OC f).obj N)) := by
  intro V y
  have h := moduleSheafFunctor_map_transitionOfRestriction_app_apply
    (overRingedSite P OC (X := X)) (cechObject P OC f) φ
    ((cechTotalRestriction P OC f).obj N) V.unop y
  refine HEq.trans (heq_of_eq h) ?_
  exact cech_moduleSheaf_map_heq P OC f (hsc := _) N
    ((Grothendieck.ιNatTrans (F := slices (cechObject P OC f)) φ.op).app
      (V.unop : ((slices (cechObject P OC f)).obj (op n) : Cat)))
    rfl ((totalForget_map_ιNatTrans_app (cechObject P OC f) φ.op _).trans (eqToHom_refl _ _).symm) y

/-- The identification of degreewise pullback with degreewise restriction along `r_φ`, between
restriction to the total site and restriction to the summand `t`, in the spelling of 0DCA. -/
abbrev cechSourceComplexIso' {m n : SimplexCategory} (φ : m ⟶ n)
    (t : ((cechObject P OC f).obj (op n)).I) :=
  Functor.isoWhiskerLeft ((cechTotalRestriction P OC f).mapHomologicalComplex (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight (Functor.isoWhiskerLeft
      (((situation (overRingedSite P OC (X := X)).J (cechObject P OC f)).componentModulesRestriction
        (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f)) m).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (NatIso.mapHomologicalComplex
        (transitionPullbackModulesIso (overRingedSite P OC (X := X)) (cechObject P OC f) φ)
        (ComplexShape.up ℤ)))
      ((summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n
        t).mapHomologicalComplex (ComplexShape.up ℤ)))

/-- The source factorization of the transition side, in the spelling of 0DCA, read through
restriction along `r_φ`. -/
abbrev cechTransitionSourceFactors' {m n : SimplexCategory} (φ : m ⟶ n)
    (t : ((cechObject P OC f).obj (op n)).I) :=
  letI := (situation (overRingedSite P OC (X := X)).J
    (cechObject P OC f)).transitionPullbackModules_preservesFiniteLimits
    (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f)) φ
    (transitionRingedToposHom_isFlat (overRingedSite P OC (X := X)) (cechObject P OC f) φ)
  Functor.compFactorization (cechTotalRestriction P OC f).mapDerivedCategoryFactors
      (Functor.compFactorization
        (Functor.compFactorization
          ((situation (overRingedSite P OC (X := X)).J
            (cechObject P OC f)).componentModulesRestriction
            (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f))
              m).mapDerivedCategoryFactors
          ((situation (overRingedSite P OC (X := X)).J
            (cechObject P OC f)).derivedTransitionPullbackFactors
            (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f)) φ
            (transitionRingedToposHom_isFlat (overRingedSite P OC (X := X)) (cechObject P OC f) φ)))
        (summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n
          t).mapDerivedCategoryFactors) ≪≫
    Functor.isoWhiskerRight (cechSourceComplexIso' P OC f φ t) DerivedCategory.Q

/-- The transition side of the compatibility of the canonical identification of summands, in the
spelling of 0DCA. -/
abbrev cechTransitionNat' {m n : SimplexCategory} (φ : m ⟶ n)
    (t : ((cechObject P OC f).obj (op n)).I) :=
  Functor.whiskerLeft (cechTotalRestriction P OC f).mapDerivedCategory
      (Functor.whiskerRight
        ((situation (overRingedSite P OC (X := X)).J
          (cechObject P OC f)).derivedComponentModuleTransition
          (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f)) φ)
        (summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n
          t).mapDerivedCategory) ≫
    (cechSummandIso P OC f n t).hom

/-- Each component of `cechSummandModulesIso` fixes sections. -/
theorem cechSummandModulesIso_hom_app_fixesSections (n : SimplexCategory)
    (t : ((cechObject P OC f).obj (op n)).I)
    (N : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (overRingedSite P OC (X := X)).O)) :
    SheafOfModules.FixesSections ((cechSummandModulesIso P OC f n t).hom.app N) :=
  canonicalSummandModulesIso_hom_app_fixesSections P OC f n t N

/-- The transformation `cechTransitionNat'` is induced by a transformation of complexes that
fixes sections in every degree. -/
theorem cechTransitionNat'_isInducedBy {m n : SimplexCategory} (φ : m ⟶ n)
    (t : ((cechObject P OC f).obj (op n)).I) :
    ∃ γ₀, NatTrans.IsInducedBy (cechTransitionSourceFactors' P OC f φ t)
      (canonicalSummandTargetFactors P OC f n t) (cechTransitionNat' P OC f φ t) γ₀ ∧
      ∀ K p, SheafOfModules.FixesSections ((γ₀.app K).f p) :=
  ⟨_, ((NatTrans.IsInducedBy.whiskerLeft _
    (((situation (overRingedSite P OC (X := X)).J
      (cechObject P OC f)).derivedComponentModuleTransition_isInducedBy
      (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f)) φ
      (transitionRingedToposHom_isFlat (overRingedSite P OC (X := X)) (cechObject P OC f)
        φ)).whiskerRight _)).comp
    (cechSummandIso_hom_isInducedBy P OC f n t)).trans_isoWhiskerRight_left
      (cechSourceComplexIso' P OC f φ t),
    Functor.fixesSections_transitionComponent _ _ _ _ _ _ _ _ _
      (hR := cechTotalRestriction_additive P OC f)
      (hCm := SimplicialSiteSituation.componentModulesRestriction_additive _ _ m)
      (hCn := SimplicialSiteSituation.componentModulesRestriction_additive _ _ n)
      (hSg := cech_summandRestriction_additive P OC f n t)
      (hH₁ := RingedSite.overMapModules_additive _ _)
      (hH₂ := RingedSite.overMapModules_additive _ _)
      (hH₃ := RingedSite.iteratedSliceTransport_additive _ _ _) _ _ _
      (fun M => (summandRestriction_map_fixesSections (overRingedSite P OC (X := X))
        (cechObject P OC f) n t
        (cech_transitionOfRestriction_fixesSections P OC f φ M)).comp
          (cechSummandModulesIso_hom_app_fixesSections P OC f n t M))⟩

/-- The pullback side of the compatibility of the canonical identification of summands. -/
abbrev cechPullbackNat (N₀ : LocalDerivedCategory.{0} (pretopologyRingedSite P OC) X)
    {m n : SimplexCategory} (φ : m ⟶ n) (t : ((cechObject P OC f).obj (op n)).I) :=
  Functor.whiskerLeft (cechTotalRestriction P OC f).mapDerivedCategory
      (Functor.associator _ _ _).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerLeft _ ((globalLocallyGiven P OC f N₀).summandDerivedPullbackIso
      (cechLift (X := pretopologyRingedSite P OC) f) φ t).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.associator _ _ _).hom _ ≫
    Functor.whiskerRight (cechSummandIso P OC f m
      (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).f t)).hom _ ≫
    globalRhoNat P OC f (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).φ t)

/-- The transformation `cechPullbackNat` is induced by a transformation of complexes that fixes
sections in every degree. -/
private theorem cechPullbackNat_isInducedBy_fixesSections
    (N₀ : LocalDerivedCategory.{0} (pretopologyRingedSite P OC) X)
    {m n : SimplexCategory} (φ : m ⟶ n) (t : ((cechObject P OC f).obj (op n)).I) :
    ∃ γ₀, NatTrans.IsInducedBy (cechTransitionSourceFactors' P OC f φ t)
      (canonicalSummandTargetFactors P OC f n t) (cechPullbackNat P OC f N₀ φ t) γ₀ ∧
      ∀ K p, SheafOfModules.FixesSections ((γ₀.app K).f p) := by
  have := cech_summandRestriction_additive P OC f m
    (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).f t)
  have := cech_summandRestriction_preservesFiniteLimits P OC f m
    (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).f t)
  have := cech_summandRestriction_preservesFiniteColimits P OC f m
    (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).f t)
  have := (globalLocallyGiven P OC f N₀).summandRestrictionB_additive
    (cechLift (X := pretopologyRingedSite P OC) f) m
    (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).f t)
  have := (globalLocallyGiven P OC f N₀).summandRestrictionB_preservesFiniteLimits
    (cechLift (X := pretopologyRingedSite P OC) f) m
    (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).f t)
  have := (globalLocallyGiven P OC f N₀).summandRestrictionB_preservesFiniteColimits
    (cechLift (X := pretopologyRingedSite P OC) f) m
    (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).f t)
  obtain ⟨γr, hr, hfr⟩ := globalRhoNat_isInducedBy P OC f
    (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).φ t)
  have a1 := NatTrans.IsInducedBy.whiskerLeft
    (cechTotalRestriction P OC f).mapDerivedCategoryFactors
    (NatTrans.IsInducedBy.associator
      ((situation (overRingedSite P OC (X := X)).J
        (cechObject P OC f)).componentModulesRestriction
        (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f))
          m).mapDerivedCategoryFactors
      ((situation (overRingedSite P OC (X := X)).J
        (cechObject P OC f)).derivedTransitionPullbackFactors
        (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f)) φ
        (transitionRingedToposHom_isFlat (overRingedSite P OC (X := X)) (cechObject P OC f) φ))
      (summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n
        t).mapDerivedCategoryFactors)
  have a2 := NatTrans.IsInducedBy.associator_inv
    (cechTotalRestriction P OC f).mapDerivedCategoryFactors
    ((situation (overRingedSite P OC (X := X)).J
      (cechObject P OC f)).componentModulesRestriction
      (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f))
        m).mapDerivedCategoryFactors
    (Functor.compFactorization ((situation (overRingedSite P OC (X := X)).J
        (cechObject P OC f)).derivedTransitionPullbackFactors
        (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f)) φ
        (transitionRingedToposHom_isFlat (overRingedSite P OC (X := X)) (cechObject P OC f) φ))
      (summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) n
        t).mapDerivedCategoryFactors)
  have b := NatTrans.IsInducedBy.whiskerLeft
    (Functor.compFactorization (cechTotalRestriction P OC f).mapDerivedCategoryFactors
      ((situation (overRingedSite P OC (X := X)).J
        (cechObject P OC f)).componentModulesRestriction
        (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f))
          m).mapDerivedCategoryFactors)
    ((globalLocallyGiven P OC f N₀).summandDerivedPullbackIso_hom_isInducedBy
      (cechLift (X := pretopologyRingedSite P OC) f) φ t)
  have a3 := NatTrans.IsInducedBy.associator_inv
    (Functor.compFactorization (cechTotalRestriction P OC f).mapDerivedCategoryFactors
      ((situation (overRingedSite P OC (X := X)).J
        (cechObject P OC f)).componentModulesRestriction
        (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f))
          m).mapDerivedCategoryFactors)
    ((globalLocallyGiven P OC f N₀).summandRestrictionB
      (cechLift (X := pretopologyRingedSite P OC) f) m
      (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).f t)).mapDerivedCategoryFactors
    ((globalLocallyGiven P OC f N₀).restrictionFactors
      (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).φ t))
  have a4 := (NatTrans.IsInducedBy.associator
    (cechTotalRestriction P OC f).mapDerivedCategoryFactors
    ((situation (overRingedSite P OC (X := X)).J
      (cechObject P OC f)).componentModulesRestriction
      (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f))
        m).mapDerivedCategoryFactors
    (summandRestriction (overRingedSite P OC (X := X)) (cechObject P OC f) m
      (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).f 
        t)).mapDerivedCategoryFactors).whiskerRight
      ((globalLocallyGiven P OC f N₀).restrictionFactors
        (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).φ t))
  have k := (cechSummandIso_hom_isInducedBy P OC f m
    (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).f t)).whiskerRight
    ((globalLocallyGiven P OC f N₀).restrictionFactors
      (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).φ t))
  exact ⟨_, (a1.comp (a2.comp (b.comp (a3.comp (a4.comp (k.comp hr)))))).trans_isoWhiskerRight_left
    (cechSourceComplexIso' P OC f φ t),
    Functor.fixesSections_pullbackComponent _ _ _ _ _ _ _ _ _ _
      (hR := cechTotalRestriction_additive P OC f)
      (hCm := SimplicialSiteSituation.componentModulesRestriction_additive _ _ m)
      (hπ := inferInstanceAs ((situation (overRingedSite P OC (X := X)).J
        (cechObject P OC f)).transitionRingedToposHom
          (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f))
            φ).toModulesHom.pullbackModules.Additive)
      (hr := by exact RingedSite.overMapModules_additive _ _)
      (hτ := cech_transitionRestriction_additive P OC f φ)
      (hSgt := cech_summandRestriction_additive P OC f n t)
      (hSgs := cech_summandRestriction_additive P OC f m
        (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).f t))
      (hH₁ := RingedSite.overMapModules_additive _ _)
      (hH₂ := RingedSite.overMapModules_additive _ _)
      (hH₃ := RingedSite.iteratedSliceTransport_additive _ _ _)
      (transitionPullbackModulesIso (overRingedSite P OC (X := X)) (cechObject P OC f) φ)
      (summandTransitionRestrictionIso (overRingedSite P OC (X := X)) (cechObject P OC f) φ t)
      (cechSummandModulesIso P OC f m
        (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).f t)) γr
      (fun M => (summandTransitionRestrictionIso_hom_app_fixesSections
        (overRingedSite P OC (X := X)) (cechObject P OC f) φ t
        _).comp (overMap_map_fixesSections (overRingedSite P OC (X := X)) _
          (cechSummandModulesIso_hom_app_fixesSections P OC f m
            (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).f t) M)))
      hfr⟩

/-- The transformation `cechPullbackNat` is induced by a transformation of complexes. -/
theorem cechPullbackNat_isInducedBy_aux
    (N₀ : LocalDerivedCategory.{0} (pretopologyRingedSite P OC) X)
    {m n : SimplexCategory} (φ : m ⟶ n) (t : ((cechObject P OC f).obj (op n)).I) :
    ∃ γ₀, NatTrans.IsInducedBy (cechTransitionSourceFactors' P OC f φ t)
      (canonicalSummandTargetFactors P OC f n t) (cechPullbackNat P OC f N₀ φ t) γ₀ :=
  (cechPullbackNat_isInducedBy_fixesSections P OC f N₀ φ t).imp fun _ h => h.1

/-- The transformation `cechPullbackNat` is induced by a transformation of complexes that fixes
sections in every degree. -/
theorem cechPullbackNat_isInducedBy (N₀ : LocalDerivedCategory.{0} (pretopologyRingedSite P OC) X)
    {m n : SimplexCategory} (φ : m ⟶ n) (t : ((cechObject P OC f).obj (op n)).I) :
    ∃ γ₀, NatTrans.IsInducedBy (cechTransitionSourceFactors' P OC f φ t)
      (canonicalSummandTargetFactors P OC f n t) (cechPullbackNat P OC f N₀ φ t) γ₀ ∧
      ∀ K p, SheafOfModules.FixesSections ((γ₀.app K).f p) :=
  cechPullbackNat_isInducedBy_fixesSections P OC f N₀ φ t

/-- **The canonical identification of summands is compatible with the transitions**, as an
equality of natural transformations in the global object. -/
theorem cechTransitionNat'_eq_cechPullbackNat
    (N₀ : LocalDerivedCategory.{0} (pretopologyRingedSite P OC) X)
    {m n : SimplexCategory} (φ : m ⟶ n) (t : ((cechObject P OC f).obj (op n)).I) :
    cechTransitionNat' P OC f φ t = cechPullbackNat P OC f N₀ φ t := by
  obtain ⟨γL, hL, hfL⟩ := cechTransitionNat'_isInducedBy P OC f φ t
  obtain ⟨γR, hR, hfR⟩ := cechPullbackNat_isInducedBy P OC f N₀ φ t
  exact RingedSite.isInducedBy_ext_of_fixesSections hL hR hfL hfR

end AlgebraicGeometry.RingedSite.CoveringGlueing

end
