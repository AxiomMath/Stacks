module

public import Mathlib.CategoryTheory.Sites.Point.Presheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkInverseImageModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkPullbackAtAPointPair
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseAcyclic
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkDerived
public import StacksFrontier.CategoryTheory.Sites.Point.Topos
public import StacksFrontier.Cotangent.HenselizationUnconditional
public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangle
public import StacksFrontier.Cotangent.SheavesOfRings.PullbackCotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseSheafification
public import StacksFrontier.Cotangent.SheavesOfRings.StalkCotangentComplex
public import StacksFrontier.Cotangent.TensorProduct
public import StacksFrontier.Homology.Injectives.FilteredComplex.InverseSystemRepresentation
public import StacksFrontier.Homology.KInjective.ChangeOfRings
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
import all StacksFrontier.Homology.PseudoCoherent.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cotangent complex of a henselization of sheaves of rings

Let `(C, J)` be a site with a conservative family `P` of points (in the sense of Mathlib's
`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints`), and let `g : R₀ ⟶ R` be a
homomorphism of sheaves of commutative rings. Suppose that at every point `Φ` of the family the
stalk map `(R₀)_Φ → R_Φ` is a henselization, or a strict henselization, of the local ring
`(R₀)_Φ` (`CategoryTheory.Sheaf.IsHenselizationAt`). Then the cotangent complex `L_{R/R₀}` of
Stacks 08SS is acyclic, so zero in `D(R)`, and so is its degreewise base change
`L_{R/R₀} ⊗_R D` along any `R ⟶ D`.

The proof is stalkwise. At a point `Φ`, module-level Stacks 05V1 and Stacks 08T0 identify the
stalk of `L_{R/R₀}` with the cotangent complex of the inverse images of `R₀` and `R` on the
one-point site; Stacks 08SX, for the trivial topology of the one-point site, identifies the
latter with the ring-level cotangent complex of the stalk rings; and items (7) and (8) of
Stacks 08R2 make that vanish. Acyclicity is then read off the stalks by the module-valued form
of Stacks 05V3. For the base change, the stalk of `L_{R/R₀} ⊗_R D` is the base change of the
stalk of `L_{R/R₀}` (Stacks 05V5), which is an acyclic bounded-above complex of projective
modules, so stays acyclic.

## Main definitions

* `CategoryTheory.Sheaf.IsHenselizationAt`: the stalk map of `g` at a point is a henselization.
* `CategoryTheory.Sheaf.stalkCotangentComplexRingIso`: the stalk of `L_{R/R₀}` at a point is a
  ring-level cotangent complex of the stalk rings.

## Main results

* `CategoryTheory.Sheaf.acyclic_cotangentComplex_of_isHenselizationAt` and
  `CategoryTheory.Sheaf.isZero_Q_obj_cotangentComplex_of_isHenselizationAt`: `L_{R/R₀} = 0`.
* `CategoryTheory.Sheaf.acyclic_baseChangedCotangentComplex_of_isHenselizationAt` and
  `CategoryTheory.Sheaf.isZero_Q_obj_baseChangedCotangentComplex_of_isHenselizationAt`:
  `L_{R/R₀} ⊗_R D = 0`.
* `CategoryTheory.Sheaf.isIso_sectionsCotangentComplexComparison_bot`: Stacks 08SX for the
  trivial topology, the comparison `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` is an isomorphism.

## Implementation notes

The points of the family are Mathlib's points `J.Point.{max u v w}`, whose fibres live in the
universe of the sections; the universe `w` is not determined by the other data and has to be
given explicitly, for instance `.{u + 1, u, 0}` on a site `C : Type (u + 1)` with morphisms in
`Type u` and sections in `Type (u + 1)`. The hypothesis is stated through models `A₀ → A` of the
stalk map so that it can be transported along ring isomorphisms; the direct form on the stalk
rings is `CategoryTheory.Sheaf.isHenselizationAt_of_isHenselization`.

## References

* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2), items (7) and (8).
* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 05V3](https://stacks.math.columbia.edu/tag/05V3)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.RingedPoint (PointSite pointSiteSheafEquiv)

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The unique object of the one-point site `Stacks.Sheaves.RingedPoint.PointSite`. -/
def pointSiteObj : PointSite.{v, u} := ULiftHom.objUp ⟨⟨PUnit.unit⟩⟩

/-- The point of the one-point site with the trivial topology attached to its unique object
(Mathlib's `CategoryTheory.GrothendieckTopology.pointBot`): its stalk functor is the evaluation
at that object. -/
abbrev pointSitePoint : (⊥ : GrothendieckTopology PointSite.{v, u}).Point.{max u v w} :=
  GrothendieckTopology.pointBot (pointSiteObj)

/-- A point `Φ` of the site `(C, J)`, read as a morphism of topoi out of the topos of the
one-point site: the point of the topos `Φ.pointOfTopos` (Stacks 00YA (1)) through
`CategoryTheory.Sheaf.pointToposMorphism`. Its inverse image is the stalk functor of `Φ`. -/
@[sga "4 IV 7.1" "more general"]
abbrev sitePointToposMorphism (Φ : J.Point.{max u v w}) :=
  pointToposMorphism.{u, v, w} J Φ.pointOfTopos

/-- A set, read as a sheaf on the one-point site through `CategoryTheory.Sheaf.pointToposEquiv`,
has the set itself as its sections over the unique object. -/
def pointToposEquivInverseSectionsIso : (pointToposEquiv.{u, v, w}).inverse ⋙
    sheafToPresheaf (⊥ : GrothendieckTopology PointSite.{v, u}) (Type (max u v w)) ⋙
    (evaluation _ _).obj (op (pointSiteObj : PointSite.{v, u})) ≅ 𝟭 (Type (max u v w)) :=
  Iso.refl _

/-- The stalk functor of `Φ` on sheaves of sets is the inverse image along
`CategoryTheory.Sheaf.sitePointToposMorphism` followed by the stalk functor of the point
`CategoryTheory.Sheaf.pointSitePoint` of the one-point site. This is the hypothesis of
module-level Stacks 05V1, `Stacks.Sheaves.StalkInverseImage.stalkNatIso`, for that morphism of
topoi. -/
def sitePointSheafFiberIso (Φ : J.Point.{max u v w}) :
    Φ.sheafFiber (A := Type (max u v w)) ≅
      (sitePointToposMorphism J Φ).inverseImage ⋙
        (pointSitePoint.{u, v, w}).sheafFiber (A := Type (max u v w)) :=
  (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft (Φ.sheafFiber (A := Type (max u v w)))
    (pointToposEquivInverseSectionsIso.{u, v, w}.symm ≪≫
      Functor.isoWhiskerLeft ((pointToposEquiv.{u, v, w}).inverse ⋙
      sheafToPresheaf (⊥ : GrothendieckTopology PointSite.{v, u}) (Type (max u v w)))
      (GrothendieckTopology.pointBotPresheafFiberIso.{max u v w} (pointSiteObj : PointSite.{v, u})
        (Type (max u v w))).symm)

end CategoryTheory.Sheaf

namespace Stacks

universe w' v' u'

variable {D : Type u'} [Category.{v'} D] [LocallySmall.{w'} D] (X : D)
  (R : Dᵒᵖ ⥤ RingCat.{w'})

/-- At the point of a category with the trivial topology attached to an object `X`, the stalk of a
presheaf of rings is its ring of sections over `X`. -/
def pointBotRingFiberIso :
    ((GrothendieckTopology.pointBot.{w'} X).presheafFiber (A := RingCat.{w'})).obj R ≅
      R.obj (op X) :=
  (GrothendieckTopology.pointBotPresheafFiberIso.{w'} X RingCat.{w'}).app R

/-- The canonical element of the fibre over `X` of the point attached to `X`: the identity. -/
def pointBotBase : (GrothendieckTopology.pointBot.{w'} X).fiber.obj X :=
  shrinkYonedaObjObjEquiv.symm (𝟙 X)

/-- The germ map at the point attached to `X`, from the sections over `X` of a presheaf of modules
to its stalk, as a linear map over the stalk ring, the sections being regarded as a module over
the stalk ring through `Stacks.pointBotRingFiberIso`. -/
def pointBotGerm (M : PresheafOfModules.{w'} R) :
    (ModuleCat.restrictScalars (pointBotRingFiberIso X R).hom.hom).obj (M.obj (op X)) →ₗ[
      ((GrothendieckTopology.pointBot.{w'} X).presheafFiber (A := RingCat.{w'})).obj R]
      (presheafModuleFiber (GrothendieckTopology.pointBot.{w'} X) R).obj M where
  toFun m := toPresheafModuleFiber _ M X (pointBotBase X) m
  map_add' := map_add _
  map_smul' r m := by
    have h := toPresheafModuleFiber_smul (GrothendieckTopology.pointBot.{w'} X) M X
      (pointBotBase X) ((pointBotRingFiberIso X R).hom.hom r) m
    refine h.trans ?_
    congr 1
    exact ConcreteCategory.congr_hom ((pointBotRingFiberIso X R).hom_inv_id) r

/-- The germ map at the point attached to `X` is bijective. -/
theorem bijective_pointBotGerm (M : PresheafOfModules.{w'} R) :
    Function.Bijective (pointBotGerm X R M) := by
  have h : IsIso ((GrothendieckTopology.pointBot.{w'} X).toPresheafFiber (A := AddCommGrpCat.{w'})
      X (pointBotBase X) M.presheaf) :=
    inferInstanceAs (IsIso (((GrothendieckTopology.pointBot.{w'} X).toPresheafFiberNatTrans
      (A := AddCommGrpCat.{w'}) X (shrinkYonedaObjObjEquiv.symm (𝟙 X))).app M.presheaf))
  exact ConcreteCategory.bijective_of_isIso
    ((GrothendieckTopology.pointBot.{w'} X).toPresheafFiber (A := AddCommGrpCat.{w'})
      X (pointBotBase X) M.presheaf)

/-- **The stalk at the point attached to an object, for the trivial topology, is the evaluation
at that object**, as modules over the stalk ring, naturally in the presheaf of modules. -/
def presheafModuleFiberPointBotIso :
    PresheafOfModules.evaluation R (op X) ⋙
        ModuleCat.restrictScalars (pointBotRingFiberIso X R).hom.hom ≅
      presheafModuleFiber (GrothendieckTopology.pointBot.{w'} X) R :=
  NatIso.ofComponents
    (fun M => (LinearEquiv.ofBijective (pointBotGerm X R M)
      (bijective_pointBotGerm X R M)).toModuleIso)
    (fun {M M'} g => by
      ext m
      exact (toPresheafModuleFiber_naturality _ g X (pointBotBase X) m).symm)

end Stacks

namespace CategoryTheory.GrothendieckTopology

universe w₁ v₁ u₁ w₂ v₂

/-- For the trivial topology, a morphism inverted by sheafification is an isomorphism. -/
theorem isIso_of_W_bot {E : Type u₁} [Category.{v₁} E] {A : Type w₁} [Category.{w₂} A]
    {P Q : Eᵒᵖ ⥤ A} (g : P ⟶ Q) (hg : (⊥ : GrothendieckTopology E).W g) : IsIso g := by
  let g' : (⟨P, Presheaf.isSheaf_bot P⟩ : Sheaf (⊥ : GrothendieckTopology E) A) ⟶
      ⟨Q, Presheaf.isSheaf_bot Q⟩ := ⟨g⟩
  have : IsIso g' := (W_sheafToPresheaf_map_iff_isIso (φ := g')).1 hg
  exact inferInstanceAs (IsIso ((sheafToPresheaf _ A).map g'))

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.Sheaf

variable {E : Type u} [Category.{v} E] {A B : Sheaf (⊥ : GrothendieckTopology E)
  CommRingCat.{max u v w}} (f : A ⟶ B)

/-- **Stacks 08SX for the trivial topology.** For a homomorphism of sheaves of commutative rings
on a category with the trivial topology, the canonical map `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` of
`CategoryTheory.Sheaf.sectionsCotangentComplexComparison` is an isomorphism of complexes of
`B(U)`-modules: it is inverted by sheafification (the sheafification clause of Stacks 08SX), and
for the trivial topology sheafification inverts only isomorphisms. -/
theorem isIso_sectionsCotangentComplexComparison_bot (U : Eᵒᵖ) :
    IsIso (sectionsCotangentComplexComparison (⊥ : GrothendieckTopology E) f U) := by
  have hc : ∀ j : ℤ, IsIso ((sectionsCotangentComplexComparison (⊥ : GrothendieckTopology E)
      f U).f j) := by
    intro j
    have h := GrothendieckTopology.isIso_of_W_bot _
      (W_sectionwiseCotangentPresheafComplexComparison_f (⊥ : GrothendieckTopology E) f j)
    have h' : IsIso (((sectionwiseCotangentPresheafComplexComparison
        (⊥ : GrothendieckTopology E) f).f j).app U) := inferInstance
    have h'' : IsIso ((forget₂ (ModuleCat _) AddCommGrpCat.{max u v w}).map
        ((sectionsCotangentComplexComparison (⊥ : GrothendieckTopology E) f U).f j)) := h'
    exact isIso_of_reflects_iso _ (forget₂ (ModuleCat _) AddCommGrpCat.{max u v w})
  exact HomologicalComplex.Hom.isIso_of_components _

end CategoryTheory.Sheaf

namespace Stacks

universe w' v' u'

variable {D : Type u'} [Category.{v'} D] [LocallySmall.{w'} D] (X : D)
  (R : Sheaf (⊥ : GrothendieckTopology D) RingCat.{w'})

/-- **The stalk at the point attached to an object, for the trivial topology, is the evaluation
at that object**, for sheaves of modules. -/
def sheafModuleFiberPointBotIso :
    SheafOfModules.evaluation R (op X) ⋙
        ModuleCat.restrictScalars (pointBotRingFiberIso X R.obj).hom.hom ≅
      sheafModuleFiber (GrothendieckTopology.pointBot.{w'} X) R :=
  Functor.isoWhiskerLeft (SheafOfModules.forget R) (presheafModuleFiberPointBotIso X R.obj)

universe t

/-- Restriction of scalars along a ring isomorphism preserves projective modules, being an
equivalence of categories. -/
theorem projective_restrictScalars_of_ringEquiv {S T : Type t} [Ring S] [Ring T] (e : S ≃+* T)
    {X : ModuleCat.{t} T} (hX : Projective X) :
    Projective ((ModuleCat.restrictScalars.{t} e.toRingHom).obj X) :=
  ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).map_projective_iff X).2 hX

end Stacks

namespace CategoryTheory.Sheaf

open Stacks.Sheaves.StalkInverseImage Stacks.Sheaves.ToposPushforward

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {R₀ R : Sheaf J CommRingCat.{max u v w}} (g : R₀ ⟶ R) (Φ : J.Point.{max u v w})

/-- The ring-level cotangent complex `L_{B(pt)/A(pt)}` of the ring map of sections at the unique
object of the one-point site of the inverse images, along the point `Φ`, of `g : R₀ ⟶ R`. -/
abbrev pointCotangentComplex :=
  CommAlgCat.cotangentComplex.{max u v w, max u v w}
    (((sitePointToposMorphism J Φ).inverseImageRing.obj R₀).obj.obj (op pointSiteObj))
    (sectionsAlgebra (⊥ : GrothendieckTopology PointSite.{v, u})
      ((sitePointToposMorphism J Φ).inverseImageRing.map g) (op pointSiteObj))

/-- **The stalk of the cotangent complex at a point is the ring-level cotangent complex of the
stalk rings.** For a point `Φ` of the site, the stalk at `Φ` of `L_{R/R₀}` is, up to restriction
of scalars along two ring isomorphisms, the ring-level cotangent complex
`CategoryTheory.Sheaf.pointCotangentComplex`. The isomorphism is the composite of module-level
Stacks 05V1 (`Stacks.Sheaves.StalkInverseImage.stalkNatIso`), Stacks 08T0
(`CategoryTheory.Sheaf.stalkCotangentComplexIso`), the stalk at the point of the one-point site
(`Stacks.sheafModuleFiberPointBotIso`) and Stacks 08SX for the trivial topology
(`CategoryTheory.Sheaf.isIso_sectionsCotangentComplexComparison_bot`). -/
def stalkCotangentComplexRingIso :
    ((Stacks.sheafModuleFiber Φ (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w}
        R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj (cotangentComplex.{u, v, w} J g) ≅
      ((ModuleCat.restrictScalars (stalkRingEquiv (sitePointToposMorphism J Φ)
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} R) pointSitePoint Φ
          (sitePointSheafFiberIso J Φ)).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.restrictScalars (Stacks.pointBotRingFiberIso (pointSiteObj : PointSite.{v, u})
          (inverseImageRingSheaf (sitePointToposMorphism J Φ)
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} R)).obj).hom.hom
          ).mapHomologicalComplex (ComplexShape.up ℤ)).obj (pointCotangentComplex J g Φ)) :=
  let q := sitePointToposMorphism J Φ
  let O := Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} R
  let σ := (stalkRingEquiv q O pointSitePoint Φ (sitePointSheafFiberIso J Φ)).toRingHom
  let Rσ := (ModuleCat.restrictScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)
  have := isIso_sectionsCotangentComplexComparison_bot.{u, v, w} (q.inverseImageRing.map g)
    (op pointSiteObj)
  (NatIso.mapHomologicalComplex (stalkNatIso q O pointSitePoint Φ (sitePointSheafFiberIso J Φ))
      (ComplexShape.up ℤ)).app (cotangentComplex.{u, v, w} J g) ≪≫
    Rσ.mapIso (((Stacks.sheafModuleFiber pointSitePoint
      (inverseImageRingSheaf q O)).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (stalkCotangentComplexIso.{u, v, w} J Φ.pointOfTopos g)) ≪≫
    Rσ.mapIso ((NatIso.mapHomologicalComplex (Stacks.sheafModuleFiberPointBotIso
      (pointSiteObj : PointSite.{v, u}) (inverseImageRingSheaf q O)) (ComplexShape.up ℤ)).symm.app
        (cotangentComplex.{u, v, w} (⊥ : GrothendieckTopology PointSite.{v, u})
          (q.inverseImageRing.map g))) ≪≫
    Rσ.mapIso (((ModuleCat.restrictScalars (Stacks.pointBotRingFiberIso
      (pointSiteObj : PointSite.{v, u}) (inverseImageRingSheaf q O).obj).hom.hom
        ).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
          (asIso (sectionsCotangentComplexComparison
          (⊥ : GrothendieckTopology PointSite.{v, u}) (q.inverseImageRing.map g)
            (op pointSiteObj))).symm)

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

open Stacks.Sheaves.StalkInverseImage Stacks.Sheaves.ToposPushforward Stacks.Sheaves.StalkTransport

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (Φ : J.Point.{max u v w})

/-- The ring of sections, over the unique object of the one-point site, of the inverse image of a
sheaf of commutative rings along a point `Φ`. -/
abbrev pointRing (X : Sheaf J CommRingCat.{max u v w}) : CommRingCat.{max u v w} :=
  ((sitePointToposMorphism J Φ).inverseImageRing.obj X).obj.obj (op pointSiteObj)

/-- The ring of sections at the point of the inverse image of a sheaf of rings `X` along `Φ` is the
`RingCat`-valued stalk of `X` at `Φ`: the transported ring structure on the stalk of the
underlying sheaf of sets is the one of the stalk (`Stacks.Sheaves.StalkTransport`). -/
def pointRingEquiv (X : Sheaf J CommRingCat.{max u v w}) :
    pointRing J Φ X ≃+* (Φ.presheafFiber (A := RingCat.{max u v w})).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} X).obj where
  toFun := ringStalkComparison Φ (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} X)
  invFun := (Equiv.ofBijective _ (bijective_ringStalkComparison Φ
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} X))).symm
  left_inv := (Equiv.ofBijective _ (bijective_ringStalkComparison Φ
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} X))).left_inv
  right_inv := (Equiv.ofBijective _ (bijective_ringStalkComparison Φ
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} X))).right_inv
  map_add' x y := ringStalkComparison_ringAddObj Φ _ x y
  map_mul' x y := ringStalkComparison_ringMulObj Φ _ x y

/-- The ring of sections at the point of the inverse image of `X` along `Φ` is the
`CommRingCat`-valued stalk of `X` at `Φ`. -/
def pointRingEquivStalk (X : Sheaf J CommRingCat.{max u v w}) :
    pointRing J Φ X ≃+* (Φ.presheafFiber (A := CommRingCat.{max u v w})).obj X.obj :=
  (pointRingEquiv J Φ X).trans (Stacks.commRingSheafFiberIso Φ X).ringCatIsoToRingEquiv

variable {J} {R₀ R : Sheaf J CommRingCat.{max u v w}} (g : R₀ ⟶ R)

/-- `CategoryTheory.Sheaf.pointRingEquivStalk` is natural: it intertwines the map of sections
induced by `g` with the map of stalks induced by `g`. -/
theorem pointRingEquivStalk_naturality (x : pointRing J Φ R₀) :
    pointRingEquivStalk J Φ R (((sitePointToposMorphism J Φ).inverseImageRing.map g).hom.app
        (op pointSiteObj) x) =
      (Φ.presheafFiber (A := CommRingCat.{max u v w})).map g.hom
        (pointRingEquivStalk J Φ R₀ x) := by
  have h0 := congrArg (fun f => f.hom.app (op (pointSiteObj : PointSite.{v, u})))
    (MorphismOfTopoi.inverseImageRing_map_forget (sitePointToposMorphism J Φ) g)
  have h1 := congrFun (congrArg (fun f => f.hom) (h0)) x
  have h2 := congrFun (congrArg (fun f => f.hom) (((Φ.presheafFiberCompIso
    (forget RingCat.{max u v w})).hom.naturality (Functor.whiskerRight g.hom
      (forget₂ CommRingCat RingCat))))) x
  have h3 := ConcreteCategory.congr_hom (((Φ.presheafFiberCompIso
    (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).hom.naturality g.hom))
  have h4 : ringStalkComparison Φ (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} R)
      ((((sitePointToposMorphism J Φ).inverseImageRing.map g).hom.app (op pointSiteObj)) x) =
      (Φ.presheafFiber (A := RingCat.{max u v w})).map
        (Functor.whiskerRight g.hom (forget₂ CommRingCat RingCat))
        (ringStalkComparison Φ (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} R₀) x) :=
    (congrArg (ringStalkComparison Φ (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} R))
      h1).trans h2
  exact (congrArg (Stacks.commRingSheafFiberIso Φ R).hom.hom h4).trans (h3 _)

/-- **The stalk map of `g` at `Φ` is a henselization.** The stalk rings
`(R₀)_Φ` and `R_Φ` (Mathlib's `CommRingCat`-valued `presheafFiber`) are identified, compatibly
with the stalk map of `g`, with a local ring `A₀` and an `A₀`-algebra `A` which is a
henselization of `A₀` with residue field some extension `L` of the residue field of `A₀`
(`IsLocalRing.IsHenselization`, Stacks 04GQ); a strict henselization is the case `L = κ^sep`. -/
def IsHenselizationAt (g : R₀ ⟶ R) (Φ : J.Point.{max u v w}) : Prop :=
  ∃ (A₀ A : Type (max u v w)) (_ : CommRing A₀) (_ : CommRing A) (_ : IsLocalRing A₀)
    (_ : IsLocalRing A) (_ : Algebra A₀ A) (L : Type (max u v w)) (_ : Field L)
    (_ : Algebra (IsLocalRing.ResidueField A₀) L) (_ : IsLocalRing.IsHenselization A₀ L A)
    (e₀ : (Φ.presheafFiber (A := CommRingCat.{max u v w})).obj R₀.obj ≃+* A₀)
    (e : (Φ.presheafFiber (A := CommRingCat.{max u v w})).obj R.obj ≃+* A),
    ∀ x, e ((Φ.presheafFiber (A := CommRingCat.{max u v w})).map g.hom x) =
      algebraMap A₀ A (e₀ x)

/-- **The ring-level cotangent complex of the stalk map of `g` at `Φ` is acyclic.** The stalk rings
`(R₀)_Φ` and `R_Φ` are identified, compatibly with the stalk map of `g`, with a ring `A₀` and an
`A₀`-algebra `A` whose cotangent complex `L_{A/A₀}` is acyclic. A henselization of a local ring,
`CategoryTheory.Sheaf.IsHenselizationAt`, is an instance, by items (7) and (8) of Stacks 08R2. -/
def IsCotangentAcyclicAt (g : R₀ ⟶ R) (Φ : J.Point.{max u v w}) : Prop :=
  ∃ (A₀ A : Type (max u v w)) (_ : CommRing A₀) (_ : CommRing A) (_ : Algebra A₀ A)
    (e₀ : (Φ.presheafFiber (A := CommRingCat.{max u v w})).obj R₀.obj ≃+* A₀)
    (e : (Φ.presheafFiber (A := CommRingCat.{max u v w})).obj R.obj ≃+* A),
    (∀ x, e ((Φ.presheafFiber (A := CommRingCat.{max u v w})).map g.hom x) =
      algebraMap A₀ A (e₀ x)) ∧
    (CommAlgCat.cotangentComplex.{max u v w, max u v w} A₀ (CommAlgCat.of A₀ A)).Acyclic

/-- The hypothesis `IsCotangentAcyclicAt` is invariant under precomposing the homomorphism with an
isomorphism of sheaves of rings: the model of the stalk map is transported along the stalk of the
isomorphism. -/
theorem IsCotangentAcyclicAt.iso_hom_comp {R₁ : Sheaf J CommRingCat.{max u v w}} (i : R₁ ≅ R₀)
    {g : R₀ ⟶ R} {Φ : J.Point.{max u v w}} (h : IsCotangentAcyclicAt g Φ) :
    IsCotangentAcyclicAt (i.hom ≫ g) Φ := by
  obtain ⟨A₀, A, _, _, _, e₀, e, he, hac⟩ := h
  refine ⟨A₀, A, inferInstance, inferInstance, inferInstance,
    ((Φ.presheafFiber (A := CommRingCat.{max u v w})).mapIso
      ((sheafToPresheaf J CommRingCat.{max u v w}).mapIso i)).commRingCatIsoToRingEquiv.trans e₀,
    e, fun x => ?_, hac⟩
  have hm : (Φ.presheafFiber (A := CommRingCat.{max u v w})).map (i.hom ≫ g).hom =
      (Φ.presheafFiber (A := CommRingCat.{max u v w})).map i.hom.hom ≫
        (Φ.presheafFiber (A := CommRingCat.{max u v w})).map g.hom :=
    (Φ.presheafFiber (A := CommRingCat.{max u v w})).map_comp i.hom.hom g.hom
  exact (congrArg (fun m => e (m.hom x)) hm).trans
    ((congrArg e (ConcreteCategory.comp_apply _ _ x)).trans (he _))

attribute [local instance] HasDerivedCategory.standard in
/-- A henselization at `Φ` has acyclic ring-level cotangent complex at `Φ`: items (7) and (8) of
Stacks 08R2. -/
theorem IsHenselizationAt.isCotangentAcyclicAt {g : R₀ ⟶ R} {Φ : J.Point.{max u v w}}
    (h : IsHenselizationAt g Φ) : IsCotangentAcyclicAt g Φ := by
  obtain ⟨A₀, A, _, _, _, _, _, L, _, _, _, e₀, e, he⟩ := h
  exact ⟨A₀, A, inferInstance, inferInstance, inferInstance, e₀, e, he, fun n =>
    CochainComplex.exactAt_of_isZero_Q _ n
      (IsLocalRing.IsHenselization.isZero_cotangentComplexDerived_unconditional (R := A₀)
        (Rh := A) L)⟩

attribute [local instance] HasDerivedCategory.standard in
/-- At a point where the ring-level cotangent complex of the stalk map is acyclic, the ring-level
cotangent complex of the sections at the point vanishes, moved along the commutative square of
ring isomorphisms `CategoryTheory.Sheaf.pointRingEquivStalk`. -/
theorem isZero_pointCotangentComplexDerived_of_isCotangentAcyclicAt
    (h : IsCotangentAcyclicAt g Φ) :
    IsZero (CommAlgCat.cotangentComplexDerived.{max u v w, max u v w} (pointRing J Φ R₀)
      (sectionsAlgebra (⊥ : GrothendieckTopology PointSite.{v, u})
        ((sitePointToposMorphism J Φ).inverseImageRing.map g) (op pointSiteObj))) := by
  obtain ⟨A₀, A, _, _, _, e₀, e, he, hac⟩ := h
  have h0 := Stacks.Injectives.isZero_Q_obj_of_acyclic _ hac
  refine CommAlgCat.isZero_cotangentComplexDerived_of_bijective_square
    ⟨((pointRingEquivStalk J Φ R₀).symm.toRingHom).comp e₀.symm.toRingHom,
      ((pointRingEquivStalk J Φ R).symm.toRingHom).comp e.symm.toRingHom, fun a => ?_⟩
    ((pointRingEquivStalk J Φ R₀).symm.bijective.comp e₀.symm.bijective)
    ((pointRingEquivStalk J Φ R).symm.bijective.comp e.symm.bijective) h0
  apply (pointRingEquivStalk J Φ R).injective
  have ha : e.symm (algebraMap A₀ A a) =
      (Φ.presheafFiber (A := CommRingCat.{max u v w})).map g.hom (e₀.symm a) := by
    have := he (e₀.symm a)
    rw [RingEquiv.apply_symm_apply] at this
    rw [← this, RingEquiv.symm_apply_apply]
  change (pointRingEquivStalk J Φ R)
      ((pointRingEquivStalk J Φ R).symm (e.symm (algebraMap A₀ A a))) =
    (pointRingEquivStalk J Φ R) ((((sitePointToposMorphism J Φ).inverseImageRing.map g).hom.app
      (op pointSiteObj)) ((pointRingEquivStalk J Φ R₀).symm (e₀.symm a)))
  rw [RingEquiv.apply_symm_apply, pointRingEquivStalk_naturality, RingEquiv.apply_symm_apply, ha]

attribute [local instance] HasDerivedCategory.standard in
/-- At a point where the stalk map is a henselization, the ring-level cotangent complex of the
sections at the point vanishes: items (7) and (8) of Stacks 08R2, moved along the commutative
square of ring isomorphisms `CategoryTheory.Sheaf.pointRingEquivStalk`. -/
theorem isZero_pointCotangentComplexDerived (h : IsHenselizationAt g Φ) :
    IsZero (CommAlgCat.cotangentComplexDerived.{max u v w, max u v w} (pointRing J Φ R₀)
      (sectionsAlgebra (⊥ : GrothendieckTopology PointSite.{v, u})
        ((sitePointToposMorphism J Φ).inverseImageRing.map g) (op pointSiteObj))) :=
  isZero_pointCotangentComplexDerived_of_isCotangentAcyclicAt Φ g h.isCotangentAcyclicAt

/-- The ring-level cotangent complex of the sections at a point where the stalk map has acyclic
ring-level cotangent complex is acyclic. -/
theorem acyclic_pointCotangentComplex_of_isCotangentAcyclicAt (h : IsCotangentAcyclicAt g Φ) :
    (pointCotangentComplex J g Φ).Acyclic := fun n =>
  CochainComplex.exactAt_of_isZero_Q _ n
    (isZero_pointCotangentComplexDerived_of_isCotangentAcyclicAt Φ g h)

/-- The ring-level cotangent complex of the sections at a point where the stalk map is a
henselization is acyclic. -/
theorem acyclic_pointCotangentComplex (h : IsHenselizationAt g Φ) :
    (pointCotangentComplex J g Φ).Acyclic :=
  acyclic_pointCotangentComplex_of_isCotangentAcyclicAt Φ g h.isCotangentAcyclicAt

/-- At a point where the stalk map has acyclic ring-level cotangent complex, the stalk complex of
`L_{R/R₀}` (over the `RingCat`-valued stalk ring) is acyclic. -/
theorem acyclic_sheafModuleFiber_cotangentComplex_of_isCotangentAcyclicAt
    (h : IsCotangentAcyclicAt g Φ) :
    (((Stacks.sheafModuleFiber Φ (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w}
        R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (cotangentComplex.{u, v, w} J g)).Acyclic := fun n =>
  ((restrictScalars_acyclic _ _ (restrictScalars_acyclic _ _
    (acyclic_pointCotangentComplex_of_isCotangentAcyclicAt Φ g h))) n).of_iso
      (stalkCotangentComplexRingIso J g Φ).symm

/-- At a point where the stalk map is a henselization, the stalk complex of `L_{R/R₀}` (over the
`RingCat`-valued stalk ring) is acyclic. -/
theorem acyclic_sheafModuleFiber_cotangentComplex (h : IsHenselizationAt g Φ) :
    (((Stacks.sheafModuleFiber Φ (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w}
        R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (cotangentComplex.{u, v, w} J g)).Acyclic :=
  acyclic_sheafModuleFiber_cotangentComplex_of_isCotangentAcyclicAt Φ g h.isCotangentAcyclicAt

/-- Every term of the stalk complex of `L_{R/R₀}` at a point is a projective module over the stalk
ring: it is, up to restriction of scalars along ring isomorphisms, a term of a ring-level
cotangent complex. -/
theorem projective_sheafModuleFiber_cotangentComplex_X (j : ℤ) :
    Projective ((Stacks.sheafModuleFiber Φ (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w}
        R)).obj ((cotangentComplex.{u, v, w} J g).X j)) :=
  Projective.of_iso ((HomologicalComplex.eval _ _ j).mapIso
      (stalkCotangentComplexRingIso J g Φ)).symm
    (Stacks.projective_restrictScalars_of_ringEquiv _
      (Stacks.projective_restrictScalars_of_ringEquiv
      (Stacks.pointBotRingFiberIso (pointSiteObj : PointSite.{v, u})
        (inverseImageRingSheaf (sitePointToposMorphism J Φ)
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} R)).obj).ringCatIsoToRingEquiv
      (CommAlgCat.projective_cotangentComplex_X _ _ j)))

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

/-- At a point where the stalk map has acyclic ring-level cotangent complex, the stalk complex of
`L_{R/R₀}` over the `CommRingCat`-valued stalk ring is acyclic. -/
theorem acyclic_sheafModuleFiberOfCommRing_cotangentComplex_of_isCotangentAcyclicAt
    (h : IsCotangentAcyclicAt g Φ) :
    (((Stacks.sheafModuleFiberOfCommRing Φ R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (cotangentComplex.{u, v, w} J g)).Acyclic :=
  restrictScalars_acyclic _ _
    (acyclic_sheafModuleFiber_cotangentComplex_of_isCotangentAcyclicAt Φ g h)

/-- At a point where the stalk map is a henselization, the stalk complex of `L_{R/R₀}` over the
`CommRingCat`-valued stalk ring is acyclic. -/
theorem acyclic_sheafModuleFiberOfCommRing_cotangentComplex (h : IsHenselizationAt g Φ) :
    (((Stacks.sheafModuleFiberOfCommRing Φ R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (cotangentComplex.{u, v, w} J g)).Acyclic :=
  acyclic_sheafModuleFiberOfCommRing_cotangentComplex_of_isCotangentAcyclicAt Φ g
    h.isCotangentAcyclicAt

/-- The stalk functor `Stacks.Sheaves.StalkPullback.sheafStalk` of the base-change interchange is
`Stacks.sheafModuleFiberOfCommRing`, by definition. -/
def sheafStalkIsoSheafModuleFiberOfCommRing (X : Sheaf J CommRingCat.{max u v w}) :
    Stacks.Sheaves.StalkPullback.sheafStalk Φ X.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} X).property ≅
      Stacks.sheafModuleFiberOfCommRing Φ X :=
  Iso.refl _

/-- The stalk of the degreewise base change, as a functor out of `targetModules J R`. -/
def stalkOfTowerExtendScalars {D : Sheaf J CommRingCat.{max u v w}} (k : R ⟶ D) :
    targetModules.{u, v, w} J R ⥤
      ModuleCat.{max u v w} ((Φ.presheafFiber (A := CommRingCat.{max u v w})).obj D.obj) :=
  towerExtendScalars.{u, v, w} J k ⋙ Stacks.sheafModuleFiberOfCommRing Φ D

/-- The base change of the stalk, as a functor out of `targetModules J R`. -/
def extendScalarsOfStalk {D : Sheaf J CommRingCat.{max u v w}} (k : R ⟶ D) :
    targetModules.{u, v, w} J R ⥤
      ModuleCat.{max u v w} ((Φ.presheafFiber (A := CommRingCat.{max u v w})).obj D.obj) :=
  Stacks.sheafModuleFiberOfCommRing Φ R ⋙
    ModuleCat.extendScalars.{max u v w, max u v w, max u v w}
      (Stacks.SitePointBaseChange.stalkRingHom k.hom Φ)

/-- `CategoryTheory.Sheaf.stalkOfTowerExtendScalars` preserves zero morphisms. -/
instance stalkOfTowerExtendScalars_preservesZeroMorphisms {D : Sheaf J CommRingCat.{max u v w}}
    (k : R ⟶ D) : (stalkOfTowerExtendScalars Φ k).PreservesZeroMorphisms :=
  ⟨fun X Y => by
    change (Stacks.sheafModuleFiberOfCommRing Φ D).map
      ((towerExtendScalars.{u, v, w} J k).map 0) = 0
    rw [(towerExtendScalars.{u, v, w} J k).map_zero]
    exact (Stacks.sheafModuleFiberOfCommRing Φ D).map_zero _ _⟩

/-- `CategoryTheory.Sheaf.extendScalarsOfStalk` preserves zero morphisms. -/
instance extendScalarsOfStalk_preservesZeroMorphisms {D : Sheaf J CommRingCat.{max u v w}}
    (k : R ⟶ D) : (extendScalarsOfStalk Φ k).PreservesZeroMorphisms :=
  ⟨fun X Y => by
    change (ModuleCat.extendScalars.{max u v w, max u v w, max u v w}
      (Stacks.SitePointBaseChange.stalkRingHom k.hom Φ)).map
        ((Stacks.sheafModuleFiberOfCommRing Φ R).map 0) = 0
    exact (congrArg (ModuleCat.extendScalars.{max u v w, max u v w, max u v w}
      (Stacks.SitePointBaseChange.stalkRingHom k.hom Φ)).map
        ((Stacks.sheafModuleFiberOfCommRing Φ R).map_zero X Y)).trans (Functor.map_zero _ _ _)⟩

/-- The stalk of the degreewise base change is the base change of the stalk: Stacks 05V5 for
sheaves of modules, `Stacks.Sheaves.StalkPullback.extendScalarsSheafStalkNatIso`. -/
def stalkOfTowerExtendScalarsIso {D : Sheaf J CommRingCat.{max u v w}} (k : R ⟶ D) :
    stalkOfTowerExtendScalars Φ k ≅ extendScalarsOfStalk Φ k :=
  Functor.isoWhiskerLeft (towerExtendScalars.{u, v, w} J k)
      (sheafStalkIsoSheafModuleFiberOfCommRing Φ D).symm ≪≫
    Stacks.Sheaves.StalkPullback.extendScalarsSheafStalkNatIso Φ k.hom
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} R).property
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).property ≪≫
    Functor.isoWhiskerRight (sheafStalkIsoSheafModuleFiberOfCommRing Φ R) _

/-- The stalk complex of `L_{R/R₀} ⊗_R D` at `Φ` is the base change along the stalk map of
`k : R ⟶ D` of the stalk complex of `L_{R/R₀}`. -/
def stalkBaseChangedCotangentComplexIso {D : Sheaf J CommRingCat.{max u v w}} (k : R ⟶ D) :
    ((Stacks.sheafModuleFiberOfCommRing Φ D).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (baseChangedCotangentComplex.{u, v, w} J g k) ≅
      ((ModuleCat.extendScalars.{max u v w, max u v w, max u v w}
        (Stacks.SitePointBaseChange.stalkRingHom k.hom Φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((Stacks.sheafModuleFiberOfCommRing Φ R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (cotangentComplex.{u, v, w} J g)) :=
  ((Stacks.sheafModuleFiberOfCommRing Φ D).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (towerExtendScalarsCotangentComplexIso.{u, v, w} J g k).symm ≪≫
    (NatIso.mapHomologicalComplex (stalkOfTowerExtendScalarsIso Φ k)
      (ComplexShape.up ℤ)).app (cotangentComplex.{u, v, w} J g)

/-- At a point where the stalk map has acyclic ring-level cotangent complex, the stalk complex of
the degreewise base change `L_{R/R₀} ⊗_R D` is acyclic: the stalk complex of `L_{R/R₀}` is an
acyclic bounded-above complex of projective modules, so its base change is acyclic. -/
theorem acyclic_sheafModuleFiberOfCommRing_baseChangedCotangentComplex_of_isCotangentAcyclicAt
    (h : IsCotangentAcyclicAt g Φ) {D : Sheaf J CommRingCat.{max u v w}} (k : R ⟶ D) :
    (((Stacks.sheafModuleFiberOfCommRing Φ D).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (baseChangedCotangentComplex.{u, v, w} J g k)).Acyclic := by
  let M := ((Stacks.sheafModuleFiberOfCommRing Φ R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (cotangentComplex.{u, v, w} J g)
  have : CochainComplex.IsStrictlyLE M 0 := (CochainComplex.isStrictlyLE_iff M 0).2 fun i hi =>
    (Stacks.sheafModuleFiberOfCommRing Φ R).map_isZero (cotangentComplex_isZero_pos J g i hi)
  have : ∀ i, Projective (M.X i) := fun i =>
    Stacks.projective_restrictScalars_of_ringEquiv
      (Stacks.commRingSheafFiberIso Φ R).symm.ringCatIsoToRingEquiv
      (projective_sheafModuleFiber_cotangentComplex_X Φ g i)
  have hext := StacksDraft.PseudoCoherence.acyclic_extendScalars_of_projective
    (Stacks.SitePointBaseChange.stalkRingHom k.hom Φ) 0 M inferInstance inferInstance
    (acyclic_sheafModuleFiberOfCommRing_cotangentComplex_of_isCotangentAcyclicAt Φ g h)
  exact fun n => (hext n).of_iso (stalkBaseChangedCotangentComplexIso Φ g k).symm

/-- At a point where the stalk map is a henselization, the stalk complex of the degreewise base
change `L_{R/R₀} ⊗_R D` is acyclic: the stalk complex of `L_{R/R₀}` is an acyclic bounded-above
complex of projective modules, so its base change is acyclic. -/
theorem acyclic_sheafModuleFiberOfCommRing_baseChangedCotangentComplex
    (h : IsHenselizationAt g Φ) {D : Sheaf J CommRingCat.{max u v w}} (k : R ⟶ D) :
    (((Stacks.sheafModuleFiberOfCommRing Φ D).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (baseChangedCotangentComplex.{u, v, w} J g k)).Acyclic :=
  acyclic_sheafModuleFiberOfCommRing_baseChangedCotangentComplex_of_isCotangentAcyclicAt Φ g
    h.isCotangentAcyclicAt k

variable {P : ObjectProperty (J.Point.{max u v w})}

/-- **The cotangent complex of a homomorphism of sheaves of rings vanishes when it vanishes
stalkwise.** If at every point `Φ` of a conservative family of points of the site the stalk map
`(R₀)_Φ → R_Φ` of `g` has acyclic ring-level cotangent complex, then `L_{R/R₀}` is acyclic: by
Stacks 08T0 the stalk of `L_{R/R₀}` at `Φ` is the ring-level cotangent complex of the stalk
map. -/
theorem acyclic_cotangentComplex_of_isCotangentAcyclicAt (hP : P.IsConservativeFamilyOfPoints)
    (hacyc : ∀ Φ, P Φ → IsCotangentAcyclicAt g Φ) :
    (cotangentComplex.{u, v, w} J g).Acyclic :=
  (Stacks.acyclic_iff_forall_acyclic_mapSheafModuleFiberOfCommRing R
    (cotangentComplex.{u, v, w} J g) hP).2 fun Φ =>
      acyclic_sheafModuleFiberOfCommRing_cotangentComplex_of_isCotangentAcyclicAt Φ.obj g
      (hacyc Φ.obj Φ.property)

/-- **The cotangent complex of a homomorphism of sheaves of rings which is a henselization at
every point of a conservative family vanishes.** If at every point `Φ` of a conservative family
of points of the site the stalk map `(R₀)_Φ → R_Φ` of `g` is a (strict) henselization of the
local ring `(R₀)_Φ`, then `L_{R/R₀}` is acyclic. Stalkwise this is items (7) and (8) of Stacks
08R2, through Stacks 08T0. -/
theorem acyclic_cotangentComplex_of_isHenselizationAt (hP : P.IsConservativeFamilyOfPoints)
    (hhens : ∀ Φ, P Φ → IsHenselizationAt g Φ) :
    (cotangentComplex.{u, v, w} J g).Acyclic :=
  acyclic_cotangentComplex_of_isCotangentAcyclicAt g hP fun Φ hΦ =>
    (hhens Φ hΦ).isCotangentAcyclicAt

/-- Under the hypotheses of `acyclic_cotangentComplex_of_isCotangentAcyclicAt`, for every
homomorphism `k : R ⟶ D` the degreewise base change `L_{R/R₀} ⊗_R D`
(`CategoryTheory.Sheaf.baseChangedCotangentComplex`) is acyclic. -/
theorem acyclic_baseChangedCotangentComplex_of_isCotangentAcyclicAt
    (hP : P.IsConservativeFamilyOfPoints) (hacyc : ∀ Φ, P Φ → IsCotangentAcyclicAt g Φ)
    {D : Sheaf J CommRingCat.{max u v w}} (k : R ⟶ D) :
    (baseChangedCotangentComplex.{u, v, w} J g k).Acyclic :=
  (Stacks.acyclic_iff_forall_acyclic_mapSheafModuleFiberOfCommRing D
    (baseChangedCotangentComplex.{u, v, w} J g k) hP).2 fun Φ =>
      acyclic_sheafModuleFiberOfCommRing_baseChangedCotangentComplex_of_isCotangentAcyclicAt Φ.obj g
      (hacyc Φ.obj Φ.property) k

/-- Under the hypotheses of `CategoryTheory.Sheaf.acyclic_cotangentComplex_of_isHenselizationAt`,
for every homomorphism `k : R ⟶ D` the degreewise base change `L_{R/R₀} ⊗_R D`
(`CategoryTheory.Sheaf.baseChangedCotangentComplex`) is acyclic. -/
theorem acyclic_baseChangedCotangentComplex_of_isHenselizationAt
    (hP : P.IsConservativeFamilyOfPoints) (hhens : ∀ Φ, P Φ → IsHenselizationAt g Φ)
    {D : Sheaf J CommRingCat.{max u v w}} (k : R ⟶ D) :
    (baseChangedCotangentComplex.{u, v, w} J g k).Acyclic :=
  acyclic_baseChangedCotangentComplex_of_isCotangentAcyclicAt g hP
    (fun Φ hΦ => (hhens Φ hΦ).isCotangentAcyclicAt) k

universe t in
/-- Under the hypotheses of `acyclic_cotangentComplex_of_isCotangentAcyclicAt`, `L_{R/R₀} = 0` in
the derived category `D(R)`, for any choice of derived category. -/
theorem isZero_Q_obj_cotangentComplex_of_isCotangentAcyclicAt
    [HasDerivedCategory.{t} (targetModules.{u, v, w} J R)] (hP : P.IsConservativeFamilyOfPoints)
    (hacyc : ∀ Φ, P Φ → IsCotangentAcyclicAt g Φ) :
    IsZero (DerivedCategory.Q.obj (cotangentComplex.{u, v, w} J g)) :=
  Stacks.Injectives.isZero_Q_obj_of_acyclic _
    (acyclic_cotangentComplex_of_isCotangentAcyclicAt g hP hacyc)

universe t in
/-- Under the hypotheses of `CategoryTheory.Sheaf.acyclic_cotangentComplex_of_isHenselizationAt`,
`L_{R/R₀} = 0` in the derived category `D(R)`, for any choice of derived category. -/
theorem isZero_Q_obj_cotangentComplex_of_isHenselizationAt
    [HasDerivedCategory.{t} (targetModules.{u, v, w} J R)] (hP : P.IsConservativeFamilyOfPoints)
    (hhens : ∀ Φ, P Φ → IsHenselizationAt g Φ) :
    IsZero (DerivedCategory.Q.obj (cotangentComplex.{u, v, w} J g)) :=
  isZero_Q_obj_cotangentComplex_of_isCotangentAcyclicAt g hP fun Φ hΦ =>
    (hhens Φ hΦ).isCotangentAcyclicAt

universe t in
/-- Under the hypotheses of `acyclic_cotangentComplex_of_isCotangentAcyclicAt`, the degreewise base
change `L_{R/R₀} ⊗_R D` is zero in the derived category `D(D)`, for any choice of derived
category. -/
theorem isZero_Q_obj_baseChangedCotangentComplex_of_isCotangentAcyclicAt
    {D : Sheaf J CommRingCat.{max u v w}} [HasDerivedCategory.{t} (targetModules.{u, v, w} J D)]
    (hP : P.IsConservativeFamilyOfPoints) (hacyc : ∀ Φ, P Φ → IsCotangentAcyclicAt g Φ)
    (k : R ⟶ D) :
    IsZero (DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, v, w} J g k)) :=
  Stacks.Injectives.isZero_Q_obj_of_acyclic _
    (acyclic_baseChangedCotangentComplex_of_isCotangentAcyclicAt g hP hacyc k)

universe t in
/-- Under the hypotheses of `CategoryTheory.Sheaf.acyclic_cotangentComplex_of_isHenselizationAt`,
the degreewise base change `L_{R/R₀} ⊗_R D` is zero in the derived category `D(D)`, for any
choice of derived category. -/
theorem isZero_Q_obj_baseChangedCotangentComplex_of_isHenselizationAt
    {D : Sheaf J CommRingCat.{max u v w}} [HasDerivedCategory.{t} (targetModules.{u, v, w} J D)]
    (hP : P.IsConservativeFamilyOfPoints) (hhens : ∀ Φ, P Φ → IsHenselizationAt g Φ)
    (k : R ⟶ D) :
    IsZero (DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, v, w} J g k)) :=
  isZero_Q_obj_baseChangedCotangentComplex_of_isCotangentAcyclicAt g hP
    (fun Φ hΦ => (hhens Φ hΦ).isCotangentAcyclicAt) k

/-- The henselization hypothesis `CategoryTheory.Sheaf.IsHenselizationAt` from the stalk rings
themselves: if the stalk rings are local and the stalk map makes `R_Φ` a henselization of
`(R₀)_Φ` with some residue field `L`, the hypothesis holds with the identity models. -/
theorem isHenselizationAt_of_isHenselization
    (h : ∃ (_ : IsLocalRing ((Φ.presheafFiber (A := CommRingCat.{max u v w})).obj R₀.obj))
      (_ : IsLocalRing ((Φ.presheafFiber (A := CommRingCat.{max u v w})).obj R.obj))
      (L : Type (max u v w)) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField
        ((Φ.presheafFiber (A := CommRingCat.{max u v w})).obj R₀.obj)) L),
      letI := ((Φ.presheafFiber (A := CommRingCat.{max u v w})).map g.hom).hom.toAlgebra
      IsLocalRing.IsHenselization ((Φ.presheafFiber (A := CommRingCat.{max u v w})).obj R₀.obj) L
        ((Φ.presheafFiber (A := CommRingCat.{max u v w})).obj R.obj)) :
    IsHenselizationAt g Φ := by
  obtain ⟨_, _, L, _, _, h⟩ := h
  let := ((Φ.presheafFiber (A := CommRingCat.{max u v w})).map g.hom).hom.toAlgebra
  exact ⟨_, _, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, L,
    inferInstance, inferInstance, h, RingEquiv.refl _, RingEquiv.refl _, fun _ => rfl⟩

end CategoryTheory.Sheaf
