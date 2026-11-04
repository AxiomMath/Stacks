module

public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenGlueing
public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenBBDGlueing
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentConservative
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory

/-!
# Transporting summandwise identifications

In Situation 0DC9, let `L` be a simplicial object of `SR(B)`. A summandwise identification of an
object `E'` of `D(O)` with the locally given objects (an
`AlgebraicGeometry.RingedSite.LocallyGiven.SummandIdentification`) transports along an
isomorphism `E ≅ E'`, and, given a second family of locally given objects isomorphic to the first
compatibly with the isomorphisms `ρ_a`, along that isomorphism of families. An object admitting
a summandwise identification has vanishing cohomology in every degree in which that of all the
locally given objects on the summands does, so it is bounded below as soon as they are uniformly
so.

## Main definitions

* `AlgebraicGeometry.RingedSite.LocallyGiven.SummandIdentification.ofIso`: transport along an
  isomorphism of objects of `D(O)`.
* `AlgebraicGeometry.RingedSite.LocallyGiven.SummandIdentification.ofObjIso`: transport along
  an isomorphism of families of locally given objects.

## Main results

* `AlgebraicGeometry.RingedSite.LocallyGiven.SummandIdentification.restriction_map_comp_rho`:
  two summandwise identifications of one object differ by isomorphisms of the locally given
  objects compatible with the isomorphisms `ρ_a`.
* `AlgebraicGeometry.RingedSite.LocallyGiven.SummandIdentification.isZero_homology`: the
  cohomology of an object with a summandwise identification vanishes in every degree in which
  that of the locally given objects on the summands does.
* `AlgebraicGeometry.RingedSite.LocallyGiven.SummandIdentification.isBoundedBelow_of_summands`:
  it is bounded below when the locally given objects on the summands are uniformly so.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SimplicialSemiRepresentable

universe u uB vB

namespace CategoryTheory

/-- Pasting the squares `nat₁`, `nat₂` and `comm`:
`Sn.map T ≫ Sn.map εn ≫ σn = P ≫ R.map (Sm.map εm ≫ σm) ≫ ρ`. -/
theorem summandIdentification_ofIso_chase {𝒞m 𝒞n 𝒟m 𝒟 : Type*} [Category 𝒞m] [Category 𝒞n]
    [Category 𝒟m] [Category 𝒟] (Pf : 𝒞m ⥤ 𝒞n) (Sn : 𝒞n ⥤ 𝒟) (Sm : 𝒞m ⥤ 𝒟m) (R : 𝒟m ⥤ 𝒟)
    {Am A'm : 𝒞m} {An A'n : 𝒞n} {Y : 𝒟} {Z : 𝒟m} (εm : Am ⟶ A'm) (εn : An ⟶ A'n)
    (T : Pf.obj Am ⟶ An) (T' : Pf.obj A'm ⟶ A'n) (P : Sn.obj (Pf.obj Am) ⟶ R.obj (Sm.obj Am))
    (P' : Sn.obj (Pf.obj A'm) ⟶ R.obj (Sm.obj A'm)) (σn : Sn.obj A'n ⟶ Y) (σm : Sm.obj A'm ⟶ Z)
    (ρ : R.obj Z ⟶ Y) (nat₁ : Pf.map εm ≫ T' = T ≫ εn)
    (nat₂ : Sn.map (Pf.map εm) ≫ P' = P ≫ R.map (Sm.map εm))
    (comm : Sn.map T' ≫ σn = P' ≫ R.map σm ≫ ρ) :
    Sn.map T ≫ Sn.map εn ≫ σn = P ≫ R.map (Sm.map εm ≫ σm) ≫ ρ := by
  rw [← Sn.map_comp_assoc, ← nat₁, Sn.map_comp_assoc, comm, reassoc_of% nat₂, R.map_comp,
    Category.assoc]

/-- Pasting `Tn ≫ σn = P ≫ R.map σm ≫ ρ` with `R.map θm ≫ ρ₂ = ρ ≫ θn` gives
`Tn ≫ σn ≫ θn = P ≫ R.map (σm ≫ θm) ≫ ρ₂`. -/
theorem summandIdentification_ofObjIso_chase {𝒟m 𝒟 : Type*} [Category 𝒟m] [Category 𝒟]
    (R : 𝒟m ⥤ 𝒟) {A B : 𝒟} {Am : 𝒟m} {Y Y₂ : 𝒟} {Z Z₂ : 𝒟m} (Tn : A ⟶ B) (σn : B ⟶ Y)
    (P : A ⟶ R.obj Am) (σm : Am ⟶ Z) (ρ : R.obj Z ⟶ Y) (θn : Y ⟶ Y₂) (θm : Z ⟶ Z₂)
    (ρ₂ : R.obj Z₂ ⟶ Y₂) (comm : Tn ≫ σn = P ≫ R.map σm ≫ ρ)
    (hθ : R.map θm ≫ ρ₂ = ρ ≫ θn) :
    Tn ≫ σn ≫ θn = P ≫ R.map (σm ≫ θm) ≫ ρ₂ := by
  rw [reassoc_of% comm, R.map_comp, Category.assoc, hθ]

/-- If `T ≫ sn.hom = P.hom ≫ R.map sm.hom ≫ ρ` and `T ≫ sn'.hom = P.hom ≫ R.map sm'.hom ≫ ρ'`, then
`R.map (sm.inv ≫ sm'.hom) ≫ ρ' = ρ ≫ sn.inv ≫ sn'.hom`. -/
theorem summandIdentification_comparison_chase {𝒟m 𝒟 : Type*} [Category 𝒟m] [Category 𝒟]
    (R : 𝒟m ⥤ 𝒟) {a b Y Y' : 𝒟} {x Z Z' : 𝒟m} (T : a ⟶ b) (P : a ≅ R.obj x) (sm : x ≅ Z)
    (sm' : x ≅ Z') (sn : b ≅ Y) (sn' : b ≅ Y') (ρ : R.obj Z ⟶ Y) (ρ' : R.obj Z' ⟶ Y')
    (h : T ≫ sn.hom = P.hom ≫ R.map sm.hom ≫ ρ) (h' : T ≫ sn'.hom = P.hom ≫ R.map sm'.hom ≫ ρ') :
    R.map (sm.inv ≫ sm'.hom) ≫ ρ' = ρ ≫ sn.inv ≫ sn'.hom := by
  rw [← cancel_epi (P.hom ≫ R.map sm.hom), Category.assoc, ← R.map_comp_assoc,
    Iso.hom_inv_id_assoc, ← h', Category.assoc, ← reassoc_of% h, Iso.hom_inv_id_assoc]

end CategoryTheory

namespace AlgebraicGeometry.RingedSite.LocallyGiven

attribute [local instance] LocallyGiven.category HasDerivedCategory.standard

variable {X : RingedSite.{u, u, u}} [X.J.toCoverage.HasPullbacks]
  {G : LocallyGiven.{0, u, u, u, uB, vB} X} {L : SimplicialObject (FormalCoproduct.{u} G.B)}

/-- **A summandwise identification transports along an isomorphism of objects of `D(O)`.** -/
def SummandIdentification.ofIso
    {E E' : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules}
    (σ : G.SummandIdentification L E') (ε : E ≅ E') : G.SummandIdentification L E where
  iso n i := (G.summandDerivedRestriction L n i).mapIso
      (((situation X.J (G.image L)).derivedComponentModuleRestriction
        (structureSheaf X (G.image L)) n).mapIso ε) ≪≫ σ.iso n i
  comm {m n} φ i :=
    summandIdentification_ofIso_chase
      ((situation X.J (G.image L)).derivedTransitionPullback (structureSheaf X (G.image L)) φ)
      (G.summandDerivedRestriction L n i) (G.summandDerivedRestriction L m ((L.map φ.op).f i))
      (G.restriction ((L.map φ.op).φ i))
      (((situation X.J (G.image L)).derivedComponentModuleRestriction
        (structureSheaf X (G.image L)) m).map ε.hom)
      (((situation X.J (G.image L)).derivedComponentModuleRestriction
        (structureSheaf X (G.image L)) n).map ε.hom)
      (((situation X.J (G.image L)).derivedComponentModuleTransition
        (structureSheaf X (G.image L)) φ).app E)
      (((situation X.J (G.image L)).derivedComponentModuleTransition
        (structureSheaf X (G.image L)) φ).app E')
      ((G.summandDerivedPullbackIso L φ i).hom.app _)
      ((G.summandDerivedPullbackIso L φ i).hom.app _) (σ.iso n i).hom
      (σ.iso m ((L.map φ.op).f i)).hom (G.rho ((L.map φ.op).φ i)).hom
      (((situation X.J (G.image L)).derivedComponentModuleTransition
        (structureSheaf X (G.image L)) φ).naturality ε.hom)
      ((G.summandDerivedPullbackIso L φ i).hom.naturality _) (σ.comm φ i)

variable (G) in
/-- The locally given objects of Situation 0DC9 with the indexing category and functor of `G`
but other objects and isomorphisms. -/
abbrev withObj (obj : ∀ U : G.B, LocalDerivedCategory.{0} X (G.u.obj U))
    (rho : ∀ {V U : G.B} (a : V ⟶ U), (derivedOverMap.{0} X (G.u.map a)).obj (obj U) ≅ obj V)
    (cocycle : ∀ {W V U : G.B} (b : W ⟶ V) (a : V ⟶ U),
      (rho (b ≫ a)).hom =
        (derivedOverMapComp.{0} X (G.u.map_comp b a).symm).hom.app (obj U) ≫
          (derivedOverMap.{0} X (G.u.map b)).map (rho a).hom ≫ (rho b).hom) :
    LocallyGiven.{0, u, u, u, uB, vB} X :=
  @LocallyGiven.mk _ G.B G.category G.u obj rho cocycle

variable {obj' : ∀ U : G.B, LocalDerivedCategory.{0} X (G.u.obj U)}
  {rho' : ∀ {V U : G.B} (a : V ⟶ U), (derivedOverMap.{0} X (G.u.map a)).obj (obj' U) ≅ obj' V}
  {cocycle' : ∀ {W V U : G.B} (b : W ⟶ V) (a : V ⟶ U),
      (rho' (b ≫ a)).hom =
        (derivedOverMapComp.{0} X (G.u.map_comp b a).symm).hom.app (obj' U) ≫
          (derivedOverMap.{0} X (G.u.map b)).map (rho' a).hom ≫ (rho' b).hom}

/-- **A summandwise identification transports along an isomorphism of the locally given
objects** compatible with the isomorphisms `ρ_a` on the arrows of `L`. -/
def SummandIdentification.ofObjIso
    {E : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules}
    (σ : G.SummandIdentification L E) (θ : ∀ U : G.B, G.obj U ≅ obj' U)
    (hθ : ∀ {m n : SimplexCategory} (φ : m ⟶ n) (i : (L.obj (op n)).I),
      (G.restriction ((L.map φ.op).φ i)).map (θ _).hom ≫ (rho' ((L.map φ.op).φ i)).hom =
        (G.rho ((L.map φ.op).φ i)).hom ≫ (θ _).hom) :
    (G.withObj obj' rho' cocycle').SummandIdentification L E where
  iso n i := σ.iso n i ≪≫ θ _
  comm {m n} φ i :=
    summandIdentification_ofObjIso_chase (G.restriction ((L.map φ.op).φ i)) _ (σ.iso n i).hom _
      (σ.iso m ((L.map φ.op).f i)).hom (G.rho ((L.map φ.op).φ i)).hom (θ _).hom (θ _).hom
      (rho' ((L.map φ.op).φ i)).hom (σ.comm φ i) (hθ φ i)

/-- **Two summandwise identifications of one object differ by an isomorphism of the locally
given objects compatible with the isomorphisms `ρ_a`**, on the summands of `L`. -/
theorem SummandIdentification.restriction_map_comp_rho
    {E : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules}
    (σ : G.SummandIdentification L E)
    (σ' : (G.withObj obj' rho' cocycle').SummandIdentification L E)
    {m n : SimplexCategory} (φ : m ⟶ n) (i : (L.obj (op n)).I) :
    (G.restriction ((L.map φ.op).φ i)).map
        ((σ.iso m ((L.map φ.op).f i)).inv ≫ (σ'.iso m ((L.map φ.op).f i)).hom) ≫
        (rho' ((L.map φ.op).φ i)).hom =
      (G.rho ((L.map φ.op).φ i)).hom ≫ (σ.iso n i).inv ≫ (σ'.iso n i).hom :=
  summandIdentification_comparison_chase (G.restriction ((L.map φ.op).φ i)) _
    ((G.summandDerivedPullbackIso L φ i).app _) (σ.iso m ((L.map φ.op).f i))
    (σ'.iso m ((L.map φ.op).f i)) (σ.iso n i) (σ'.iso n i) _ _ (σ.comm φ i) (σ'.comm φ i)

/-- **The cohomology of an object with a summandwise identification vanishes in a degree as soon
as that of every locally given object on a summand does.** -/
theorem SummandIdentification.isZero_homology
    {E : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules}
    (σ : G.SummandIdentification L E) (q : ℤ)
    (h : ∀ (n : SimplexCategory) (i : (L.obj (op n)).I),
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (G.obj ((L.obj (op n)).obj i)))) :
    IsZero ((DerivedCategory.homologyFunctor ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules q).obj E) :=
  (situation X.J (G.image L)).isZero_of_forall_isZero_componentModulesRestriction
      (structureSheaf X (G.image L)) _ fun n =>
    isZero_of_forall_isZero_summandRestriction X (G.image L) n _ fun i => by
      have := G.summandRestrictionB_additive L n i
      have := G.summandRestrictionB_preservesFiniteLimits L n i
      have := G.summandRestrictionB_preservesFiniteColimits L n i
      exact (h n i).of_iso ((G.summandRestrictionB L n i).mapIso
          ((((situation X.J (G.image L)).componentModulesRestriction
            (structureSheaf X (G.image L)) n).mapDerivedCategoryHomologyFunctorIso q).app E).symm ≪≫
        (((G.summandRestrictionB L n i).mapDerivedCategoryHomologyFunctorIso q).app
          ((((situation X.J (G.image L)).componentModulesRestriction
            (structureSheaf X (G.image L)) n).mapDerivedCategory).obj E)).symm ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso (σ.iso n i))

/-- **An object with a summandwise identification is bounded below** as soon as the locally
given objects on the summands are uniformly bounded below. -/
theorem SummandIdentification.isBoundedBelow_of_summands
    {E : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules}
    (σ : G.SummandIdentification L E) (t : ℤ)
    (h : ∀ (n : SimplexCategory) (i : (L.obj (op n)).I) (q : ℤ), q < t →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (G.obj ((L.obj (op n)).obj i)))) :
    DerivedCategoryB.IsBoundedBelow E :=
  ⟨t, fun q hq => σ.isZero_homology q fun n i => h n i q hq⟩

end AlgebraicGeometry.RingedSite.LocallyGiven

end
