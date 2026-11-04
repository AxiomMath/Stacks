module

public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableTransitionFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.RestrictScalarsEquivalence
public import
    StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaCaseBSummand
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianSections
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalFibrewise

/-!
# The transitions of a simplicial semi-representable ringed site, read summandwise

Let `(C, O_C)` be a ringed site and `K` a simplicial semi-representable object of `C`, with
`K_n = {U_{n,i}}_{i ∈ I_n}`. A simplex map `φ : [m] ⟶ [n]` gives the morphism
`K(φ) : K_n ⟶ K_m` of semi-representable objects, that is, a map `α : I_n ⟶ I_m` together with
morphisms `a_i : U_{n,i} ⟶ U_{m, α(i)}`, and the relocalization functor `r_φ : C/K_n ⥤ C/K_m`
which sends `V ⟶ U_{n,i}` to `V ⟶ U_{n,i} ⟶ U_{m,α(i)}`.

Restriction of sheaves of `O_m`-modules along `r_φ` is a functor `Mod(O_m) ⥤ Mod(O_n)`, and on
the `i`-th summand of `C/K_n` it is the restriction of the `α(i)`-th summand along `a_i`. This is
the sense in which "the product decomposition is compatible with the morphisms in the simplicial
semi-representable object `K`" in the proof of Stacks 0DCA.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.transitionSiteFunctor`: the relocalization functor
  `r_φ : C/K_n ⥤ C/K_m`.
* `CategoryTheory.SimplicialSemiRepresentable.transitionRestriction`: restriction of
  `O_m`-modules along `r_φ`.
* `CategoryTheory.SimplicialSemiRepresentable.summandTransitionRestrictionIso`: on the `i`-th
  summand, restriction along `r_φ` is restriction of the `α(i)`-th summand along `a_i`.
* `CategoryTheory.SimplicialSemiRepresentable.transitionRestrictionAdjunction`: restriction
  along `r_φ` is left adjoint to the direct image along the cocontinuous functor `r_φ`.

## References

* [Stacks Project, Tag 0DCA](https://stacks.math.columbia.edu/tag/0DCA)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SemiRepresentable

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

variable (X : RingedSite.{u, u, u}) [X.J.toCoverage.HasPullbacks]
  (K : SimplicialObject (FormalCoproduct.{u} X.C))

/-- The relocalization functor `r_φ : C/K_n ⥤ C/K_m` of a simplex map `φ : [m] ⟶ [n]`, between
the component sites of the simplicial ringed site. -/
def transitionSiteFunctor {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentRingedTopos X K n).C ⥤ (componentRingedTopos X K m).C :=
  componentOverMap (K.map φ.op)

/-- The relocalization functor `r_φ : C/K_n ⥤ C/K_m` is continuous. -/
instance transitionSiteFunctor_isContinuous {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionSiteFunctor X K φ).IsContinuous (componentRingedTopos X K n).J
      (componentRingedTopos X K m).J :=
  componentOverMap_isContinuous' X.J K φ

/-- The localization functors are compatible with relocalization, on morphisms. -/
theorem sliceForget_map_transitionSiteFunctor {m n : SimplexCategory} (φ : m ⟶ n)
    {V W : ((slices K).obj (op n) : Cat)} (f : V ⟶ W) :
    (sliceForget K (op m)).map ((transitionSiteFunctor X K φ).map f) =
      (sliceForget K (op n)).map f := by
  refine (Functor.congr_hom (componentOverMap_comp_componentOverForget (K.map φ.op)) f).trans ?_
  exact (congrArg (fun k => k ≫ _ ≫ _) (rfl : eqToHom _ = 𝟙 _)).trans
    ((Category.id_comp _).trans ((congrArg (fun k => _ ≫ k) (rfl : eqToHom _ = 𝟙 _)).trans
      (Category.comp_id _)))

/-- The restriction of `O_m` along `r_φ` is `O_n`, sectionwise. -/
def transitionRingMap {m n : SimplexCategory} (φ : m ⟶ n) :
    componentRing X K n ⟶
      ((transitionSiteFunctor X K φ).sheafPushforwardContinuous RingCat.{u}
        (componentRingedTopos X K n).J (componentRingedTopos X K m).J).obj
        (componentRing X K m) :=
  ⟨{ app := fun _ => 𝟙 _
     naturality := fun _ _ f =>
      (Category.comp_id _).trans ((congrArg
        (fun g : _ ⟶ _ => (forget₂ CommRingCat RingCat).map (X.O.obj.map g.op))
        ((totalForget_map_ι X K (op n) f.unop).trans
          ((sliceForget_map_transitionSiteFunctor X K φ f.unop).symm.trans
            (totalForget_map_ι X K (op m) _).symm))).trans (Category.id_comp _).symm) }⟩

/-- **Restriction of `O_m`-modules along the relocalization functor `r_φ`.** -/
def transitionRestriction {m n : SimplexCategory} (φ : m ⟶ n) :
    SheafOfModules.{u} (componentRing X K m) ⥤ SheafOfModules.{u} (componentRing X K n) :=
  SheafOfModules.pushforward (transitionRingMap X K φ)

/-- **On the `i`-th summand, restriction along `r_φ` is restriction of the `α(i)`-th summand
along `a_i : U_{n,i} ⟶ U_{m,α(i)}`.** Both are restriction of sections along the same functor
`C/U_{n,i} ⥤ C/K_m`, so the comparison is the identity on sections. -/
def summandTransitionRestrictionIso {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (K.obj (op n)).I) :
    transitionRestriction X K φ ⋙ summandRestriction X K n i ≅
      summandRestriction X K m ((K.map φ.op).f i) ⋙
        SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          ((K.map φ.op).φ i) :=
  NatIso.ofComponents (fun M => (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) fun _ _ _ => rfl)) fun f => by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl

/-- The case-(B) ring transition of `a⁻¹O_C` is sectionwise the identity: the cross-fibre arrows
of the total site lie over identities of `C`. -/
theorem ringTransitionB_app {m n : SimplexCategory} (φ : m ⟶ n) (V) :
    (CocontinuousSimplicialSite.ringTransitionB (simplicialSite X.J K) (structureSheaf X K) φ).app V
      = 𝟙 _ := by
  have h := totalForget_map_ιNatTrans_app K (b := φ.op) (V.unop : ((slices K).obj (op n) : Cat))
  exact (congrArg (fun g : _ ⟶ _ => (forget₂ CommRingCat RingCat).map (X.O.obj.map g.op)) h).trans
    ((congrArg (fun g => (forget₂ CommRingCat RingCat).map g) (X.O.obj.map_id _)).trans
      ((forget₂ CommRingCat RingCat).map_id _))

/-- The relocalization functor is cocontinuous (Stacks 0D85). -/
instance transitionSiteFunctor_isCocontinuous {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionSiteFunctor X K φ).IsCocontinuous
      (componentRingedTopos X K n).J (componentRingedTopos X K m).J :=
  CocontinuousSimplicialSite.isCocontinuous_transitionFunctorB (simplicialSite X.J K) φ

/-- The relocalization functor is cocontinuous, at the case-(B) spelling. -/
instance transitionFunctorB_isCocontinuous' {m n : SimplexCategory} (φ : m ⟶ n) :
    (CocontinuousSimplicialSite.transitionFunctorB (simplicialSite X.J K) φ).IsCocontinuous
      (componentRingedTopos X K n).J (componentRingedTopos X K m).J :=
  CocontinuousSimplicialSite.isCocontinuous_transitionFunctorB (simplicialSite X.J K) φ

/-- The case-(B) ring transition of `a⁻¹O_C`, read at the spelling of the component ringed
topoi. -/
abbrev transitionRingInv {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionSiteFunctor X K φ).op ⋙ (componentRing X K m).obj ⟶ (componentRing X K n).obj :=
  CocontinuousSimplicialSite.ringTransitionB (simplicialSite X.J K) (structureSheaf X K) φ

/-- `transitionRingMap` on underlying presheaves of rings. -/
abbrev transitionRingMapPresheaf {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentRing X K n).obj ⟶ (transitionSiteFunctor X K φ).op ⋙ (componentRing X K m).obj :=
  (transitionRingMap X K φ).hom

/-- `transitionRingMapPresheaf` followed by `transitionRingInv` is the identity of `O_n`. -/
theorem transitionRingMap_comp_transitionRingInv {m n : SimplexCategory} (φ : m ⟶ n) :
    transitionRingMapPresheaf X K φ ≫ transitionRingInv X K φ = 𝟙 _ :=
  NatTrans.ext (funext fun V => (Category.id_comp _).trans (ringTransitionB_app X K φ V))

/-- `transitionRingInv` followed by `transitionRingMapPresheaf` is the identity of the restriction
of `O_m` along `r_φ`. -/
theorem transitionRingInv_comp_transitionRingMap {m n : SimplexCategory} (φ : m ⟶ n) :
    transitionRingInv X K φ ≫ transitionRingMapPresheaf X K φ = 𝟙 _ :=
  NatTrans.ext (funext fun V => (Category.comp_id _).trans (ringTransitionB_app X K φ V))

/-- Restriction of scalars along the two mutually inverse ring transitions. -/
def transitionScalarsEquivalence {m n : SimplexCategory} (φ : m ⟶ n) :=
  PresheafOfModules.restrictScalarsEquivalence.{u} (transitionRingMapPresheaf X K φ)
    (transitionRingInv X K φ) (transitionRingMap_comp_transitionRingInv X K φ)
    (transitionRingInv_comp_transitionRingMap X K φ)

open Stacks.SheafOfModules in
/-- Restriction of presheaves of modules along `r_φ` is left adjoint to the right Kan extension. -/
def transitionPresheafAdjunction {m n : SimplexCategory} (φ : m ⟶ n) :=
  (RestrictRan.adjunction.{u} (transitionSiteFunctor X K φ) (componentRing X K m).obj).comp
    (transitionScalarsEquivalence X K φ).toAdjunction

/-- The relocalization functor is cocontinuous, at a mixed spelling of the component sites. -/
instance transitionFunctorB_isCocontinuous'' {m n : SimplexCategory} (φ : m ⟶ n) :
    (CocontinuousSimplicialSite.transitionFunctorB (simplicialSite X.J K) φ).IsCocontinuous
      (componentRingedTopos X K n).J
      ((CocontinuousSimplicialSite.situation (simplicialSite X.J K)).componentTopology m) :=
  CocontinuousSimplicialSite.isCocontinuous_transitionFunctorB (simplicialSite X.J K) φ

/-- The direct-image form `O_m ⟶ {}_{s r_φ} O_n` of the structure map of `f_φ`, at the spelling of
the component ringed topoi: the structure map `fSharpB` of case (B). -/
def transitionFSharp {m n : SimplexCategory} (φ : m ⟶ n) :
    componentRing X K m ⟶
      ((transitionSiteFunctor X K φ).sheafPushforwardCocontinuous RingCat.{u}
        (componentRingedTopos X K n).J (componentRingedTopos X K m).J).obj
        (componentRing X K n) :=
  CocontinuousSimplicialSite.fSharpB (simplicialSite X.J K) (structureSheaf X K) φ

open Stacks.SheafOfModules in
/-- The direct image of modules along `f_φ`, read as the direct image along the cocontinuous
relocalization functor `r_φ`. -/
abbrev transitionDirectImage {m n : SimplexCategory} (φ : m ⟶ n) :
    SheafOfModules.{u} (componentRing X K n) ⥤ SheafOfModules.{u} (componentRing X K m) :=
  pushforwardCocontinuous.{u} (transitionSiteFunctor X K φ) (transitionFSharp X K φ)

open Stacks.SheafOfModules in
/-- The right adjoint of `transitionPresheafAdjunction`, on sheaves, is the direct image along the
cocontinuous transition functor of case (B): restriction of scalars moves past the Kan
extension. -/
def transitionRightAdjointIso {m n : SimplexCategory} (φ : m ⟶ n) :
    SheafOfModules.forget.{u} _ ⋙ (transitionScalarsEquivalence X K φ).inverse ⋙
        ranPushforward.{u} (transitionSiteFunctor X K φ)
          (RestrictRan.unitRingHom (transitionSiteFunctor X K φ)) ≅
      transitionDirectImage X K φ ⋙ SheafOfModules.forget.{u} _ :=
  Functor.isoWhiskerLeft (SheafOfModules.forget.{u} _)
    (RestrictRan.ranPushforwardRestrictScalarsIso.{u} (transitionSiteFunctor X K φ)
      (transitionRingInv X K φ))

/-- Restriction of a sheaf of modules along `r_φ` is restriction of its underlying presheaf of
modules, on the nose. -/
def transitionLeftIso {m n : SimplexCategory} (φ : m ⟶ n) :
    SheafOfModules.forget.{u} _ ⋙ PresheafOfModules.pushforward₀ (transitionSiteFunctor X K φ)
        (componentRing X K m).obj ⋙ (transitionScalarsEquivalence X K φ).functor ≅
      transitionRestriction X K φ ⋙ SheafOfModules.forget.{u} _ :=
  Iso.refl _

open Stacks.SheafOfModules in
/-- **Restriction along `r_φ` is left adjoint to the direct image along `f_φ`**, in the form of
the direct image along the cocontinuous transition functor of case (B). The ring transition of
`a⁻¹O_C` being sectionwise the identity, restriction of scalars along it and along
`transitionRingMap` are inverse equivalences, and the adjunction is the restriction–Kan-extension
adjunction composed with that equivalence. -/
def transitionRestrictionAdjunction {m n : SimplexCategory} (φ : m ⟶ n) :
    transitionRestriction X K φ ⊣ transitionDirectImage X K φ :=
  (transitionPresheafAdjunction X K φ).restrictFullyFaithful
    (SheafOfModules.fullyFaithfulForget.{u} _) (SheafOfModules.fullyFaithfulForget.{u} _)
    (transitionLeftIso X K φ) (transitionRightAdjointIso X K φ)

/-- The unit of `transitionRestrictionAdjunction`, on underlying presheaves of modules. -/
theorem forget_map_transitionRestrictionAdjunction_unit_app {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{u} (componentRing X K m)) :
    (SheafOfModules.forget.{u} _).map ((transitionRestrictionAdjunction X K φ).unit.app M) =
      (transitionPresheafAdjunction X K φ).unit.app ((SheafOfModules.forget.{u} _).obj M) ≫
        (transitionRightAdjointIso X K φ).hom.app ((transitionRestriction X K φ).obj M) := by
  unfold transitionRestrictionAdjunction
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [transitionLeftIso, Iso.refl_hom, NatTrans.id_app]
  exact congrArg (fun k => _ ≫ k ≫ _) (CategoryTheory.Functor.map_id _ _) |>.trans
    (congrArg (fun k => _ ≫ k) (Category.id_comp _))

end CategoryTheory.SimplicialSemiRepresentable
