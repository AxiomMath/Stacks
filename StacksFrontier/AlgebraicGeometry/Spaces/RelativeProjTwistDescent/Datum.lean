module

public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.ConormalInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationSchemeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.TwistComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.Presentation

/-!
# The descent datum of the twists of a relative Proj

In Situation 0849 let `P = Proj_X(𝒜)` be the relative homogeneous spectrum of Stacks 084B and
`X = U/R` a presentation of its base, so that `P = P_U/P_R` with `P_U = U ×_X P`,
`P_R = R ×_X P` (`AlgebraicGeometry.Space.RelativeProjPoints.presentation`).  The twist `𝒪(n)` of
Stacks 01NR lives on the scheme of every base change `V ×_X P = Proj_V(v^*𝒜)`, and the comparison
morphisms of Stacks 084B (3) carry the twists into each other
(`AlgebraicGeometry.Space.RelativeProjSituation.pointTwistComparison`).  This file turns those
comparisons into the scheme transition `t^*𝒪(n) ≅ s^*𝒪(n)` on `P_R` and proves its cocycle and unit
conditions, which is what `AlgebraicGeometry.Space.presentationDescendedModule` (Stacks 03M3) needs
to descend `𝒪(n)` to `P` (Stacks 084D).

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjPoints.LiesOver`: a morphism of base changes lying over a
  morphism of test objects; it is then the comparison morphism of Stacks 084B (3)
  (`…LiesOver.eq_eqToHom_comp_fibreComparison`).
* `AlgebraicGeometry.Space.pullbackIsoOfSquare`: the comparison `y^*(ι^*M) ≅ ι'^*M'` along a
  commutative square of schemes, and `AlgebraicGeometry.Space.gradedPieceIso` the degree-`n`
  piece of a comparison of sheaves of graded algebras.
* `AlgebraicGeometry.Space.RelativeProjSituation.twistPieceQcoh`: `𝒪(n)` on the scheme of
  `V ×_X P`, as a quasi-coherent module, and `…twistPieceComparison`: the comparison of twists
  along a morphism of base changes lying over a morphism of test objects.

## Main results

* `AlgebraicGeometry.Space.schemeTransitionReindex_comp`: reindexing a scheme transition along a
  composite.
* `AlgebraicGeometry.Space.pullbackIsoOfSquare_comp`: the comparisons along commutative squares
  compose (pseudofunctoriality of the inverse image).
* `AlgebraicGeometry.Space.RelativeProjSituation.twistPieceComparison_comp`: **the cocycle of the
  comparisons of twists** (in degree `n`, as modules).
* `AlgebraicGeometry.Space.RelativeProjSituation.schemeTransitionReindex_twistPieceComparison`:
  the reindexing of a transition `T_{t'} ≫ T_{s'}⁻¹` along a morphism lying over the relation.
* `AlgebraicGeometry.Space.RelativeProjSituation.schemeTransitionReindex_cocycle` and
  `…schemeTransitionReindex_unit`: **the cocycle and unit conditions of the transition of the
  twists**, at variables (the shape of `AlgebraicGeometry.Space.PresentationSchemeCocycle` and
  `…PresentationSchemeUnit`).

## Implementation notes

The twist lives on `Proj_V(v^*𝒜)` and the quasi-coherent modules of the descent on the scheme of
the object `V ×_X P` of the site; these are the same scheme, but every equation that compares the
two spellings of a module object costs a deep unfolding.  The twist is therefore read on the latter
through the pullback along the identity `toRelativeProj` (whose type alone crosses the spellings),
so that all module objects are spelled natively; the comparisons are transported along the
commutative squares of `toRelativeProj` by `pullbackIsoOfSquare`.  Every result is proved at
variable points of the base: instantiating the presentation-specific morphisms (for instance
`presentationTarget`) inside the comparisons exhausts the kernel's budget.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)

namespace AlgebraicGeometry.Space

/-! ### Auxiliary identities -/

/-- Cancelling an identity on the left. -/
private theorem comp_eq_of_eq_id {C : Type*} [Category C] {X Y : C} (i : X ⟶ X) (hi : i = 𝟙 X)
    (f : X ⟶ Y) : i ≫ f = f := by
  rw [hi, Category.id_comp]

/-- The identification of the pullbacks of modules along a morphism and itself is the
identity. -/
private theorem pullbackCongr_hom_app_self {Y Z : Scheme.{u}} {f : Z ⟶ Y} (h : f = f)
    (M : Y.Modules) : (Scheme.Modules.pullbackCongr h).hom.app M = 𝟙 _ :=
  rfl

/-! ### Reindexing a scheme transition along a composite -/

section Reindex

/-- The associativity of the contractions. -/
private theorem pullbackComp_inv_app_assoc {X Y Z Z' : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ Z') (M : Z'.Modules) :
    (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) =
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M ≫ eqToHom (by rw [Category.assoc]) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M := by
  have hT := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at hT
  have key : (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) =
      (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M ≫ eqToHom (by rw [Category.assoc]) ≫
          (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M := by
    refine (cancel_epi ((Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M))).1 ?_
    simp only [Category.assoc]
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, reassoc_of% hT]
    simp
  rw [key]
  simp

/-- The associativity of the contractions, second form. -/
private theorem pullbackComp_comp_right_inv_app_assoc {X Y Z Z' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ Z')
    (M : Z'.Modules) :
    (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
          (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) =
      eqToHom (by rw [Category.assoc]) ≫ (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M := by
  have hT := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at hT
  refine (cancel_mono ((Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M)).1 ?_
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact hT

/-- The associativity of the contractions, third form. -/
private theorem pullbackComp_comp_left_inv_app_assoc {X Y Z Z' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ Z')
    (M : Z'.Modules) :
    (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M ≫
        (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) =
      eqToHom (by rw [Category.assoc]) ≫ (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) := by
  have h' := pullbackComp_comp_right_inv_app_assoc f g h M
  refine (cancel_mono ((Scheme.Modules.pullbackComp f g).hom.app
    ((Scheme.Modules.pullback h).obj M))).1 ?_
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [h']
  simp

/-- The scheme form of `AlgebraicGeometry.Space.schemeTransitionReindex_comp`, at variables: the
pullback of a morphism `τ : t^*M ⟶ s^*M` along a composite `f ≫ g`, between the contractions of
the pullbacks, is the pullback along `f` of its pullback along `g`. -/
private theorem pullbackComp_inv_map_pullbackComp_hom_comp {W V R U : Scheme.{u}} (f : W ⟶ V)
    (g : V ⟶ R) (t s : R ⟶ U) (M : U.Modules)
    (τ : (Scheme.Modules.pullback t).obj M ⟶ (Scheme.Modules.pullback s).obj M) :
    (Scheme.Modules.pullbackComp (f ≫ g) t).inv.app M ≫ (Scheme.Modules.pullback (f ≫ g)).map τ ≫
        (Scheme.Modules.pullbackComp (f ≫ g) s).hom.app M =
      eqToHom (by rw [Category.assoc]) ≫ (Scheme.Modules.pullbackComp f (g ≫ t)).inv.app M ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g t).inv.app M ≫
          (Scheme.Modules.pullback g).map τ ≫
          (Scheme.Modules.pullbackComp g s).hom.app M) ≫
          (Scheme.Modules.pullbackComp f (g ≫ s)).hom.app M ≫
            eqToHom (by rw [Category.assoc]) := by
  have h1 : (Scheme.Modules.pullbackComp f (g ≫ t)).inv.app M ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g t).inv.app M) =
      eqToHom (by rw [Category.assoc]) ≫ (Scheme.Modules.pullbackComp (f ≫ g) t).inv.app M ≫
        (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback t).obj M) := by
    rw [pullbackComp_comp_left_inv_app_assoc]
    simp
  have h2 : (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g s).hom.app M) ≫
      (Scheme.Modules.pullbackComp f (g ≫ s)).hom.app M =
      (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback s).obj M) ≫
      (Scheme.Modules.pullbackComp (f ≫ g) s).hom.app M ≫
        eqToHom (by rw [Category.assoc]) := by
    rw [← cancel_epi ((Scheme.Modules.pullbackComp f g).inv.app _)]
    simp [reassoc_of% pullbackComp_inv_app_assoc f g s M]
  have hnat := (Scheme.Modules.pullbackComp f g).hom.naturality τ
  simp only [Functor.comp_map] at hnat
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% hnat]
  simp

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The underlying morphism of the identification of two pullbacks along equal morphisms. -/
private theorem eqToHom_hom_quasicoherentPullbackObj {V U : BigFppfOver B S hS} {k₁ k₂ : V ⟶ U}
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) (e : k₁ = k₂) :
    (eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) e)).hom =
      eqToHom (congrArg (fun k => (Scheme.Modules.pullback
        ((BigFppfOver.toScheme B S hS).map k)).obj M.obj) e) := by
  subst e
  rfl

variable {U R : BigFppfOver B S hS} (t s : R ⟶ U)
  (M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
  (τ : quasicoherentPullbackObj B S hS t M ⟶ quasicoherentPullbackObj B S hS s M)

/-- **The reindexing of a scheme transition along a composite `ψ ≫ x` is the pullback along `ψ`
of its reindexing along `x`**, between the contractions of the pullbacks and the identifications
`(ψ ≫ x) ≫ t = ψ ≫ (x ≫ t)`. -/
theorem schemeTransitionReindex_comp {V V' : BigFppfOver B S hS} (ψ : V' ⟶ V) (x : V ⟶ R) :
    schemeTransitionReindex B S hS t s M τ (ψ ≫ x) =
      eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) (Category.assoc ψ x t)) ≫
        (quasicoherentPullbackCompIso B S hS ψ (x ≫ t) M).inv ≫
          quasicoherentPullbackMap B S hS ψ (schemeTransitionReindex B S hS t s M τ x) ≫
            (quasicoherentPullbackCompIso B S hS ψ (x ≫ s) M).hom ≫
              eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M)
                (Category.assoc ψ x s).symm) := by
  refine ObjectProperty.hom_ext _ ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  exact pullbackComp_inv_map_pullbackComp_hom_comp _ _ _ _ M.obj τ.hom

/-- The pullback of a composite of morphisms of quasi-coherent modules is the composite of the
pullbacks. -/
@[reassoc]
theorem quasicoherentPullbackMap_comp {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (φ : M ⟶ N) (ψ : N ⟶ K) :
    quasicoherentPullbackMap B S hS g (φ ≫ ψ) =
      quasicoherentPullbackMap B S hS g φ ≫ quasicoherentPullbackMap B S hS g ψ :=
  ObjectProperty.hom_ext _ (Functor.map_comp _ _ _)

/-- The pullback of the identity of a quasi-coherent module is the identity. -/
theorem quasicoherentPullbackMap_id {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    quasicoherentPullbackMap B S hS g (𝟙 M) = 𝟙 _ :=
  ObjectProperty.hom_ext _ (CategoryTheory.Functor.map_id _ _)

/-- The pullback of an isomorphism of quasi-coherent modules. -/
def quasicoherentPullbackMapIso {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory} (e : M ≅ N) :
    quasicoherentPullbackObj B S hS g M ≅ quasicoherentPullbackObj B S hS g N where
  hom := quasicoherentPullbackMap B S hS g e.hom
  inv := quasicoherentPullbackMap B S hS g e.inv
  hom_inv_id := by rw [← quasicoherentPullbackMap_comp, e.hom_inv_id, quasicoherentPullbackMap_id]
  inv_hom_id := by rw [← quasicoherentPullbackMap_comp, e.inv_hom_id, quasicoherentPullbackMap_id]

/-- **The reindexing of a transition made of comparisons, along a morphism `x`**: if the
comparisons `αtt`, `αss` along `x ≫ t` and `x ≫ s` are those along `t` and `s` pulled back along
`x` and contracted, followed by a common `αx`, the reindexing of `αt ≫ αs⁻¹` along `x` is
`αtt ≫ αss⁻¹`. -/
theorem schemeTransitionReindex_eq_of_comp {W : BigFppfOver B S hS} (x : W ⟶ R)
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj R).ringCatSheaf).FullSubcategory}
    {E : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory}
    (αt : quasicoherentPullbackObj B S hS t M ≅ N) (αs : quasicoherentPullbackObj B S hS s M ≅ N)
    (αx : quasicoherentPullbackObj B S hS x N ≅ E)
    (αtt : quasicoherentPullbackObj B S hS (x ≫ t) M ≅ E)
    (αss : quasicoherentPullbackObj B S hS (x ≫ s) M ≅ E)
    (ht : αtt.hom.hom =
      (Scheme.Modules.pullbackCongr ((BigFppfOver.toScheme B S hS).map_comp x t)).hom.app M.obj ≫
        (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map x)
          ((BigFppfOver.toScheme B S hS).map t)).inv.app M.obj ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map x)).map αt.hom.hom ≫
            αx.hom.hom)
    (hs : αss.hom.hom =
      (Scheme.Modules.pullbackCongr ((BigFppfOver.toScheme B S hS).map_comp x s)).hom.app M.obj ≫
        (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map x)
          ((BigFppfOver.toScheme B S hS).map s)).inv.app M.obj ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map x)).map αs.hom.hom ≫
            αx.hom.hom) :
    schemeTransitionReindex B S hS t s M (αt.hom ≫ αs.inv) x = αtt.hom ≫ αss.inv := by
  have ht' : αtt.hom = (quasicoherentPullbackCompIso B S hS x t M).inv ≫
      quasicoherentPullbackMap B S hS x αt.hom ≫ αx.hom := by
    have h₁ : (Scheme.Modules.pullbackCongr
        ((BigFppfOver.toScheme B S hS).map_comp x t)).hom.app M.obj = 𝟙 _ :=
      pullbackCongr_hom_app_self _ _
    exact ObjectProperty.hom_ext _ (ht.trans (comp_eq_of_eq_id _ h₁ _))
  have hs' : αss.hom = (quasicoherentPullbackCompIso B S hS x s M).inv ≫
      quasicoherentPullbackMap B S hS x αs.hom ≫ αx.hom := by
    have h₁ : (Scheme.Modules.pullbackCongr
        ((BigFppfOver.toScheme B S hS).map_comp x s)).hom.app M.obj = 𝟙 _ :=
      pullbackCongr_hom_app_self _ _
    exact ObjectProperty.hom_ext _ (hs.trans (comp_eq_of_eq_id _ h₁ _))
  have hs'' : αss.inv = αx.inv ≫ quasicoherentPullbackMap B S hS x αs.inv ≫
      (quasicoherentPullbackCompIso B S hS x s M).hom := by
    rw [← cancel_epi αss.hom, Iso.hom_inv_id, hs']
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← quasicoherentPullbackMap_comp_assoc, Iso.hom_inv_id, quasicoherentPullbackMap_id]
    simp
  unfold schemeTransitionReindex
  rw [quasicoherentPullbackMap_comp, ht', hs'']
  simp

/-- `AlgebraicGeometry.Space.schemeTransitionReindex_eq_of_comp` with the underlying morphisms of
the comparisons named. -/
theorem schemeTransitionReindex_eq_of_comp_of_hom_eq {W : BigFppfOver B S hS} (x : W ⟶ R)
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj R).ringCatSheaf).FullSubcategory}
    {E : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory}
    (αt : quasicoherentPullbackObj B S hS t M ≅ N) (αs : quasicoherentPullbackObj B S hS s M ≅ N)
    (αx : quasicoherentPullbackObj B S hS x N ≅ E)
    (αtt : quasicoherentPullbackObj B S hS (x ≫ t) M ≅ E)
    (αss : quasicoherentPullbackObj B S hS (x ≫ s) M ≅ E)
    (βt : (quasicoherentPullbackObj B S hS t M).obj ⟶ N.obj) (hβt : αt.hom.hom = βt)
    (βs : (quasicoherentPullbackObj B S hS s M).obj ⟶ N.obj) (hβs : αs.hom.hom = βs)
    (βx : (quasicoherentPullbackObj B S hS x N).obj ⟶ E.obj) (hβx : αx.hom.hom = βx)
    (βtt : (quasicoherentPullbackObj B S hS (x ≫ t) M).obj ⟶ E.obj) (hβtt : αtt.hom.hom = βtt)
    (βss : (quasicoherentPullbackObj B S hS (x ≫ s) M).obj ⟶ E.obj) (hβss : αss.hom.hom = βss)
    (ht : βtt =
      (Scheme.Modules.pullbackCongr ((BigFppfOver.toScheme B S hS).map_comp x t)).hom.app M.obj ≫
        (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map x)
          ((BigFppfOver.toScheme B S hS).map t)).inv.app M.obj ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map x)).map βt ≫ βx)
    (hs : βss =
      (Scheme.Modules.pullbackCongr ((BigFppfOver.toScheme B S hS).map_comp x s)).hom.app M.obj ≫
        (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map x)
          ((BigFppfOver.toScheme B S hS).map s)).inv.app M.obj ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map x)).map βs ≫ βx) :
    schemeTransitionReindex B S hS t s M (αt.hom ≫ αs.inv) x = αtt.hom ≫ αss.inv := by
  subst hβt hβs hβx hβtt hβss
  exact schemeTransitionReindex_eq_of_comp B S hS t s M x αt αs αx αtt αss ht hs

end Reindex

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X}
  (d : RelativeProjPoints B S hS π)

/-! ### Morphisms of base changes lying over a morphism of test objects -/

/-- Two morphisms into the base change `T ×_X P` agree as soon as their structure morphisms to `T`
and their morphisms to `P` do. -/
theorem fibre_hom_ext {V T : BigFppfOver B S hS} {f : yoneda.obj T ⟶ X}
    {y₁ y₂ : V ⟶ d.fibre T f} (h₁ : y₁ ≫ d.fibreHom T f = y₂ ≫ d.fibreHom T f)
    (h₂ : yoneda.map y₁ ≫ d.fibreToSpace T f = yoneda.map y₂ ≫ d.fibreToSpace T f) : y₁ = y₂ :=
  Yoneda.fullyFaithful.map_injective ((d.isPullback T f).hom_ext h₂
    (by rw [← Functor.map_comp, ← Functor.map_comp, h₁]))

/-- A morphism `T' ×_X P ⟶ T ×_X P` of base changes **lies over** a morphism `k : T' ⟶ T` of test
objects if it commutes with the structure morphisms to `T'` and `T` and with the morphisms to
`P`. -/
def LiesOver {T T' : BigFppfOver B S hS} {f : yoneda.obj T ⟶ X} {f' : yoneda.obj T' ⟶ X}
    (y : d.fibre T' f' ⟶ d.fibre T f) (k : T' ⟶ T) : Prop :=
  y ≫ d.fibreHom T f = d.fibreHom T' f' ≫ k ∧
    yoneda.map y ≫ d.fibreToSpace T f = d.fibreToSpace T' f'

/-- **A morphism into the base change `T ×_X P`** from a morphism `a` to `T` and a morphism `b` to
`P` over the same point of `X`. -/
noncomputable def fibreLift {V T : BigFppfOver B S hS} {f : yoneda.obj T ⟶ X} (a : V ⟶ T)
    (b : yoneda.obj V ⟶ P) (w : b ≫ π = yoneda.map a ≫ f) : V ⟶ d.fibre T f :=
  Yoneda.fullyFaithful.preimage ((d.isPullback T f).lift b (yoneda.map a) w)

/-- The lift lies over `a`. -/
theorem fibreLift_comp_fibreHom {V T : BigFppfOver B S hS} {f : yoneda.obj T ⟶ X} (a : V ⟶ T)
    (b : yoneda.obj V ⟶ P) (w : b ≫ π = yoneda.map a ≫ f) :
    d.fibreLift a b w ≫ d.fibreHom T f = a :=
  Yoneda.fullyFaithful.map_injective (by
    rw [Functor.map_comp, fibreLift, Yoneda.fullyFaithful.map_preimage]
    exact (d.isPullback T f).lift_snd _ _ _)

/-- The lift lies over `b`. -/
theorem map_fibreLift_comp_fibreToSpace {V T : BigFppfOver B S hS} {f : yoneda.obj T ⟶ X}
    (a : V ⟶ T) (b : yoneda.obj V ⟶ P) (w : b ≫ π = yoneda.map a ≫ f) :
    yoneda.map (d.fibreLift a b w) ≫ d.fibreToSpace T f = b := by
  rw [fibreLift, Yoneda.fullyFaithful.map_preimage]
  exact (d.isPullback T f).lift_fst _ _ _

variable {d}

/-- The comparison morphism of Stacks 084B (3) along `k` lies over `k`. -/
theorem liesOver_fibreComparison (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (k : T' ⟶ T) : d.LiesOver (d.fibreComparison T f k) k :=
  ⟨d.fibreComparison_comp_fibreHom T f k, d.map_fibreComparison_comp_fibreToSpace T f k⟩

/-- Precomposing with the identification of the base changes along two equal points preserves
lying over `k`. -/
theorem LiesOver.eqToHom_comp {T T' : BigFppfOver B S hS} {f : yoneda.obj T ⟶ X}
    {f₁ f₂ : yoneda.obj T' ⟶ X} (e : f₁ = f₂) {y : d.fibre T' f₂ ⟶ d.fibre T f} {k : T' ⟶ T}
    (hy : d.LiesOver y k) : d.LiesOver (eqToHom (congrArg (d.fibre T') e) ≫ y) k := by
  subst e
  simpa using hy

/-- Lying over is compatible with composition. -/
theorem LiesOver.comp {T T' T'' : BigFppfOver B S hS} {f : yoneda.obj T ⟶ X}
    {f' : yoneda.obj T' ⟶ X} {f'' : yoneda.obj T'' ⟶ X} {y : d.fibre T' f' ⟶ d.fibre T f}
    {y' : d.fibre T'' f'' ⟶ d.fibre T' f'} {k : T' ⟶ T} {k' : T'' ⟶ T'}
    (hy : d.LiesOver y k) (hy' : d.LiesOver y' k') : d.LiesOver (y' ≫ y) (k' ≫ k) :=
  ⟨by rw [Category.assoc, hy.1, ← Category.assoc, hy'.1, Category.assoc],
    by rw [Functor.map_comp, Category.assoc, hy.2, hy'.2]⟩

/-- Two morphisms of base changes lying over the same morphism agree. -/
theorem LiesOver.eq {T T' : BigFppfOver B S hS} {f : yoneda.obj T ⟶ X}
    {f' : yoneda.obj T' ⟶ X} {y₁ y₂ : d.fibre T' f' ⟶ d.fibre T f} {k₁ k₂ : T' ⟶ T}
    (hy₁ : d.LiesOver y₁ k₁) (hy₂ : d.LiesOver y₂ k₂) (hk : k₁ = k₂) : y₁ = y₂ :=
  d.fibre_hom_ext (by rw [hy₁.1, hy₂.1, hk]) (by rw [hy₁.2, hy₂.2])

/-- **A morphism of base changes lying over `k` is the comparison morphism of Stacks 084B (3)
along `k`**, after identifying the two spellings of the point. -/
theorem LiesOver.eq_eqToHom_comp_fibreComparison {T T' : BigFppfOver B S hS}
    {f : yoneda.obj T ⟶ X} {f' : yoneda.obj T' ⟶ X} {y : d.fibre T' f' ⟶ d.fibre T f}
    {k : T' ⟶ T} (hy : d.LiesOver y k) (hf : yoneda.map k ≫ f = f') :
    y = eqToHom (congrArg (d.fibre T') hf).symm ≫ d.fibreComparison T f k := by
  subst hf
  exact hy.eq ((liesOver_fibreComparison T f k).eqToHom_comp rfl) rfl

end RelativeProjPoints

/-! ### Auxiliary identities -/


open Stacks.AlgebraicGeometry.RelativeProjTwists (SchemeGradedAlgebra) in
/-- **The degree-`n` piece of a comparison `f^*G ≅ N` of sheaves of graded algebras**, as an
isomorphism `f^*(G_n) ≅ N_n` of modules on the scheme. -/
def gradedPieceIso {X Y : Scheme.{u}} (f : Y ⟶ X) {G : SchemeGradedAlgebra X}
    {N : SchemeGradedAlgebra Y} (e : pbAlgS f G ≅ N) (n : ℤ) :
    (Scheme.Modules.pullback f).obj (G.piece n) ≅ (N.piece n : Y.Modules) :=
  SheafOfModules.GradedAlgebra.pieceIsoOfIso e n

open Stacks.AlgebraicGeometry.RelativeProjTwists (SchemeGradedAlgebra) in
open Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp in
/-- The degree-`n` piece of a composite comparison of sheaves of graded algebras of the shape of
the cocycle of the comparisons of twists, at variables. -/
theorem gradedPieceIso_hom_eq_of_eq_trans {X₃ X₂ X₁ : Scheme.{u}} (a : X₃ ⟶ X₂)
    (b : X₂ ⟶ X₁) (c : X₃ ⟶ X₁) (hc : c = a ≫ b) {G : SchemeGradedAlgebra X₁}
    {N : SchemeGradedAlgebra X₂} {E : SchemeGradedAlgebra X₃} (n : ℤ) (T : pbAlgS b G ≅ N)
    (T' : pbAlgS a N ≅ E) (T'' : pbAlgS c G ≅ E)
    (h : T'' = pullbackGradedAlgebraCongrIso G hc ≪≫ (pullbackGradedAlgebraCompIso G a b).symm ≪≫
      Stacks.RingedSpace.pullbackGradedAlgebraMapIso _ T ≪≫ T') :
    (gradedPieceIso c T'' n).hom =
      (Scheme.Modules.pullbackCongr hc).hom.app (G.piece n) ≫
        (Scheme.Modules.pullbackComp a b).inv.app (G.piece n) ≫
          (Scheme.Modules.pullback a).map (gradedPieceIso b T n).hom ≫
            (gradedPieceIso a T' n).hom := by
  subst h
  rfl

/-! ### Isomorphisms of modules on a scheme, read in the category of sheaves of modules -/

/-- An isomorphism of modules on a scheme, read as an isomorphism of sheaves of modules over the
structure sheaf. -/
def modulesIsoToSheafOfModules {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    @Iso (SheafOfModules.{u} X.ringCatSheaf) _ M N where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- The underlying morphism of an isomorphism of a full subcategory built from an isomorphism of
the underlying objects. -/
private theorem isoMk_hom_hom {C : Type*} [Category C] {P : ObjectProperty C}
    {a b : P.FullSubcategory} (e : a.obj ≅ b.obj) : (P.isoMk e).hom.hom = e.hom :=
  rfl

/-- The underlying morphism of the pullback of a morphism of quasi-coherent modules. -/
private theorem quasicoherentPullbackMap_hom (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory} (φ : M ⟶ N) :
    (quasicoherentPullbackMap B S hS g φ).hom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).map φ.hom :=
  rfl

/-- The underlying morphism of the inverse of the contraction of two pullbacks. -/
private theorem quasicoherentPullbackCompIso_inv_hom (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {W V U : BigFppfOver B S hS} (h : W ⟶ V) (g : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (quasicoherentPullbackCompIso B S hS h g M).inv.hom =
      (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map h)
        ((BigFppfOver.toScheme B S hS).map g)).inv.app M.obj :=
  rfl

/-- The underlying morphism of a composite in a full subcategory of sheaves of modules on a
scheme, read in the category of modules on the scheme. -/
theorem fullSubcategory_comp_hom_eq {X : Scheme.{u}}
    {P : ObjectProperty (SheafOfModules.{u} X.ringCatSheaf)} {a b c : P.FullSubcategory}
    (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).hom = @CategoryStruct.comp X.Modules _ a.obj b.obj c.obj f.hom g.hom :=
  rfl

/-! ### Comparisons along commutative squares of schemes -/

section PullbackSquare

variable {X' X Y' Y Z' Z : Scheme.{u}}

/-- The identification of the pullbacks of a module along two equal morphisms is the transport
along the equality. -/
private theorem pullbackCongr_hom_app_eq_eqToHom {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M = eqToHom (by rw [h]) := by
  subst h
  rfl

/-- The contraction `f^*(g^*M) ≅ (f ≫ g)^*M` is natural in `g` along an equality. -/
private theorem pullbackComp_inv_app_map_eqToHom (f : X ⟶ Y) {g₁ g₂ : Y ⟶ Z} (e : g₁ = g₂)
    (M : Z.Modules) :
    (Scheme.Modules.pullbackComp f g₁).inv.app M ≫
        (Scheme.Modules.pullback f).map (eqToHom (by rw [e]) :
          (Scheme.Modules.pullback g₁).obj M ⟶ (Scheme.Modules.pullback g₂).obj M) =
      eqToHom (by rw [e]) ≫ (Scheme.Modules.pullbackComp f g₂).inv.app M := by
  subst e
  simp

/-- The contraction `f^*(g^*M) ≅ (f ≫ g)^*M` is natural in `f` along an equality. -/
private theorem pullbackComp_inv_app_eqToHom {f₁ f₂ : X ⟶ Y} (e : f₁ = f₂) (g : Y ⟶ Z)
    (M : Z.Modules) :
    (Scheme.Modules.pullbackComp f₁ g).inv.app M ≫
        (eqToHom (by rw [e]) :
          (Scheme.Modules.pullback f₁).obj ((Scheme.Modules.pullback g).obj M) ⟶
            (Scheme.Modules.pullback f₂).obj ((Scheme.Modules.pullback g).obj M)) =
      eqToHom (by rw [e]) ≫ (Scheme.Modules.pullbackComp f₂ g).inv.app M := by
  subst e
  simp

/-- **The comparison along a commutative square.**  For a square `y ≫ ιX = ιY ≫ pc` and an
isomorphism `T : pc^*M ≅ M'`, the isomorphism `y^*(ιX^*M) ≅ ιY^*M'`: the contraction of the two
pullbacks along the square, followed by the pullback of `T` along `ιY`. -/
def pullbackIsoOfSquare (ιX : X' ⟶ X) (ιY : Y' ⟶ Y) (y : Y' ⟶ X') (pc : Y ⟶ X)
    (e : y ≫ ιX = ιY ≫ pc) {M : X.Modules} {M' : Y.Modules}
    (T : (Scheme.Modules.pullback pc).obj M ≅ M') :
    (Scheme.Modules.pullback y).obj ((Scheme.Modules.pullback ιX).obj M) ≅
      (Scheme.Modules.pullback ιY).obj M' :=
  (Scheme.Modules.pullbackComp y ιX).app M ≪≫ (Scheme.Modules.pullbackCongr e).app M ≪≫
    ((Scheme.Modules.pullbackComp ιY pc).app M).symm ≪≫ (Scheme.Modules.pullback ιY).mapIso T

/-- **The comparisons along commutative squares compose.**  For squares `y ≫ ιU = ιV ≫ pc` and
`y' ≫ ιV = ιW ≫ pc'`, their composite `yy = y' ≫ y`, `pc'' = pc' ≫ pc`, and an isomorphism `T''`
along `pc''` which is `T` pulled back along `pc'` followed by `T'`, the comparison along the
composite square is the comparison along the first, pulled back along `y'`, followed by the
comparison along the second. -/
theorem pullbackIsoOfSquare_comp {U' U V' V W' W : Scheme.{u}} (ιU : U' ⟶ U) (ιV : V' ⟶ V)
    (ιW : W' ⟶ W) (y : V' ⟶ U') (y' : W' ⟶ V') (yy : W' ⟶ U') (hyy : yy = y' ≫ y)
    (pc : V ⟶ U) (pc' : W ⟶ V) (pc'' : W ⟶ U) (hpc : pc'' = pc' ≫ pc)
    (eV : y ≫ ιU = ιV ≫ pc) (eW : y' ≫ ιV = ιW ≫ pc') (eW'' : yy ≫ ιU = ιW ≫ pc'')
    {MU : U.Modules} {MV : V.Modules} {MW : W.Modules}
    (T : (Scheme.Modules.pullback pc).obj MU ≅ MV)
    (T' : (Scheme.Modules.pullback pc').obj MV ≅ MW)
    (T'' : (Scheme.Modules.pullback pc'').obj MU ≅ MW)
    (hT : T''.hom = (Scheme.Modules.pullbackCongr hpc).hom.app MU ≫
      (Scheme.Modules.pullbackComp pc' pc).inv.app MU ≫
        (Scheme.Modules.pullback pc').map T.hom ≫ T'.hom) :
    (pullbackIsoOfSquare ιU ιW yy pc'' eW'' T'').hom =
      (Scheme.Modules.pullbackCongr hyy).hom.app ((Scheme.Modules.pullback ιU).obj MU) ≫
        (Scheme.Modules.pullbackComp y' y).inv.app ((Scheme.Modules.pullback ιU).obj MU) ≫
          (Scheme.Modules.pullback y').map (pullbackIsoOfSquare ιU ιV y pc eV T).hom ≫
            (pullbackIsoOfSquare ιV ιW y' pc' eW T').hom := by
  subst hyy hpc
  simp only [pullbackIsoOfSquare, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, hT, pullbackCongr_hom_app_eq_eqToHom, Category.assoc,
    eqToHom_refl, Category.id_comp]
  have n1 := (Scheme.Modules.pullbackComp y' ιV).hom.naturality T.hom
  have n2 := (Scheme.Modules.pullbackCongr eW).hom.naturality T.hom
  have n3 := (Scheme.Modules.pullbackComp ιW pc').inv.naturality T.hom
  simp only [Functor.comp_map, pullbackCongr_hom_app_eq_eqToHom] at n1 n2 n3
  rw [reassoc_of% n1, reassoc_of% n2, reassoc_of% n3]
  rw [reassoc_of% (pullbackComp_inv_app_assoc y' y ιU MU),
    reassoc_of% (pullbackComp_inv_app_map_eqToHom y' eV MU),
    reassoc_of% (pullbackComp_comp_right_inv_app_assoc y' ιV pc MU),
    reassoc_of% (pullbackComp_inv_app_eqToHom eW pc MU),
    reassoc_of% (pullbackComp_comp_left_inv_app_assoc ιW pc' pc MU)]
  simp only [eqToHom_trans_assoc]

/-- `AlgebraicGeometry.Space.pullbackIsoOfSquare`, read as an isomorphism of sheaves of modules
over the structure sheaf. -/
def pullbackSheafIsoOfSquare (ιX : X' ⟶ X) (ιY : Y' ⟶ Y) (y : Y' ⟶ X') (pc : Y ⟶ X)
    (e : y ≫ ιX = ιY ≫ pc) {M : X.Modules} {M' : Y.Modules}
    (T : (Scheme.Modules.pullback pc).obj M ≅ M') :
    @Iso (SheafOfModules.{u} Y'.ringCatSheaf) _
      ((Scheme.Modules.pullback y).obj ((Scheme.Modules.pullback ιX).obj M))
      ((Scheme.Modules.pullback ιY).obj M') :=
  modulesIsoToSheafOfModules (pullbackIsoOfSquare ιX ιY y pc e T)

/-- `AlgebraicGeometry.Space.pullbackIsoOfSquare_comp` for
`AlgebraicGeometry.Space.pullbackSheafIsoOfSquare`. -/
theorem pullbackSheafIsoOfSquare_comp {U' U V' V W' W : Scheme.{u}} (ιU : U' ⟶ U) (ιV : V' ⟶ V)
    (ιW : W' ⟶ W) (y : V' ⟶ U') (y' : W' ⟶ V') (yy : W' ⟶ U') (hyy : yy = y' ≫ y)
    (pc : V ⟶ U) (pc' : W ⟶ V) (pc'' : W ⟶ U) (hpc : pc'' = pc' ≫ pc)
    (eV : y ≫ ιU = ιV ≫ pc) (eW : y' ≫ ιV = ιW ≫ pc') (eW'' : yy ≫ ιU = ιW ≫ pc'')
    {MU : U.Modules} {MV : V.Modules} {MW : W.Modules}
    (T : (Scheme.Modules.pullback pc).obj MU ≅ MV)
    (T' : (Scheme.Modules.pullback pc').obj MV ≅ MW)
    (T'' : (Scheme.Modules.pullback pc'').obj MU ≅ MW)
    (hT : T''.hom = (Scheme.Modules.pullbackCongr hpc).hom.app MU ≫
      (Scheme.Modules.pullbackComp pc' pc).inv.app MU ≫
        (Scheme.Modules.pullback pc').map T.hom ≫ T'.hom) :
    (pullbackSheafIsoOfSquare ιU ιW yy pc'' eW'' T'').hom =
      (Scheme.Modules.pullbackCongr hyy).hom.app ((Scheme.Modules.pullback ιU).obj MU) ≫
        (Scheme.Modules.pullbackComp y' y).inv.app ((Scheme.Modules.pullback ιU).obj MU) ≫
          (Scheme.Modules.pullback y').map (pullbackSheafIsoOfSquare ιU ιV y pc eV T).hom ≫
            (pullbackSheafIsoOfSquare ιV ιW y' pc' eW T').hom :=
  pullbackIsoOfSquare_comp ιU ιV ιW y y' yy hyy pc pc' pc'' hpc eV eW eW'' T T' T'' hT

end PullbackSquare

/-! ### Telescoping transitions through a common trivialization -/

/-- **The cocycle condition of transitions that factor through a common trivialization.**  If each
of three transitions `σ` is `Θ_a ≫ Θ_b⁻¹` for isomorphisms `Θ` to a common object, indexed so
that the endpoints match, the first is the composite of the other two. -/
private theorem eq_eqToHom_comp_of_trivialization {𝒞 : Type*} [Category 𝒞] {J K : Type*}
    (Q : J → 𝒞) (ι : K → J) {E : 𝒞} (Θ : ∀ k, Q (ι k) ≅ E)
    {aCt aCs a1t a1s a2t a2s : J} (kCt kCs k1t k1s k2t k2s : K)
    (pCt : aCt = ι kCt) (pCs : aCs = ι kCs) (p1t : a1t = ι k1t) (p1s : a1s = ι k1s)
    (p2t : a2t = ι k2t) (p2s : a2s = ι k2s)
    (h1 : kCt = k1t) (h2 : k1s = k2t) (h3 : k2s = kCs)
    (e1 : aCt = a1t) (e2 : a1s = a2t) (e3 : a2s = aCs)
    (σC : Q aCt ⟶ Q aCs) (σ1 : Q a1t ⟶ Q a1s) (σ2 : Q a2t ⟶ Q a2s)
    (hC : σC = eqToHom (congrArg Q pCt) ≫ (Θ kCt).hom ≫ (Θ kCs).inv ≫
      eqToHom (congrArg Q pCs.symm))
    (hσ1 : σ1 = eqToHom (congrArg Q p1t) ≫ (Θ k1t).hom ≫ (Θ k1s).inv ≫
      eqToHom (congrArg Q p1s.symm))
    (hσ2 : σ2 = eqToHom (congrArg Q p2t) ≫ (Θ k2t).hom ≫ (Θ k2s).inv ≫
      eqToHom (congrArg Q p2s.symm)) :
    σC = eqToHom (congrArg Q e1) ≫ σ1 ≫ eqToHom (congrArg Q e2) ≫ σ2 ≫
      eqToHom (congrArg Q e3) := by
  subst hC hσ1 hσ2 h1 h2 h3 pCt pCs p1t p1s p2t p2s
  simp

/-- **The unit condition of a transition that factors through a trivialization**: if `σ` is
`Θ_a ≫ Θ_b⁻¹` with equal indices `a = b`, it is the identification of its endpoints. -/
private theorem eq_eqToHom_of_trivialization {𝒞 : Type*} [Category 𝒞] {J K : Type*}
    (Q : J → 𝒞) (ι : K → J) {E : 𝒞} (Θ : ∀ k, Q (ι k) ≅ E) {a b : J} (ka kb : K)
    (pa : a = ι ka) (pb : b = ι kb) (h : ka = kb) (e : a = b) (σ : Q a ⟶ Q b)
    (hσ : σ = eqToHom (congrArg Q pa) ≫ (Θ ka).hom ≫ (Θ kb).inv ≫
      eqToHom (congrArg Q pb.symm)) :
    σ = eqToHom (congrArg Q e) := by
  subst hσ h pa pb
  simp

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- The comparison morphism of Stacks 084B (3) along `h` lies over `h`. -/
theorem liesOver_projComparison {Z Z' : BigFppfOver s.site s.base s.containsBase}
    (g : yoneda.obj Z ⟶ s.space.1) (h : Z' ⟶ Z) :
    s.relativeProjPoints.LiesOver
      (s.quadrupleRestriction.projComparison s.shrink.contains_relativeProj_pointAlgebra g h) h :=
  ⟨(s.isPullback_projComparison g h).1.w, (s.isPullback_projComparison g h).2.1⟩

/-- **A morphism of base changes lying over `k` is, on schemes, the identification of the
restrictions followed by the base-change morphism of Tag 01O3**, the form in which
`AlgebraicGeometry.Space.RelativeProjSituation.pointTwistComparison` takes it. -/
theorem toScheme_map_eq_of_liesOver {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} {k : V ⟶ U}
    (hv : yoneda.map k ≫ u = v)
    {y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u}
    (hy : s.relativeProjPoints.LiesOver y k) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map y =
      (relativeProjCongr (A₁ := s.shrink.pointAlgebra V v)
        (A₂ := (s.shrink.pointAlgebra U u).pullback
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k))
        (s.quadrupleRestriction.restrict k u v hv)
        (s.quadrupleRestriction.isIso_restrict_app k u v hv)).hom ≫
        baseChangeHom (s.shrink.pointAlgebra U u)
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k) := by
  rw [hy.eq ((s.liesOver_projComparison u k).eqToHom_comp hv.symm) rfl]
  exact s.toScheme_map_eqToHom_projComparison u k v hv

/-- A morphism of base changes lying over `k` commutes with the structure morphisms of the two
relative homogeneous spectra. -/
theorem toScheme_map_comp_toBase_of_liesOver {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} {k : V ⟶ U}
    (hv : yoneda.map k ≫ u = v)
    {y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u}
    (hy : s.relativeProjPoints.LiesOver y k) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map y ≫
        (relativeProj (s.shrink.pointAlgebra U u)).toBase =
      (relativeProj (s.shrink.pointAlgebra V v)).toBase ≫
        (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k := by
  rw [hy.eq ((s.liesOver_projComparison u k).eqToHom_comp hv.symm) rfl]
  exact s.toScheme_map_eqToHom_projComparison_comp_toBase u k v hv

/-- The scheme of `V ×_X P` is `Proj_V(v^*𝒜)`: the identity, read as a morphism from the former
to the latter. -/
def toRelativeProj (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre V v) ⟶
      (relativeProj (s.shrink.pointAlgebra V v)).scheme :=
  𝟙 _

/-- A morphism of base changes, read on the relative homogeneous spectra, commutes with
`AlgebraicGeometry.Space.RelativeProjSituation.toRelativeProj`. -/
theorem map_comp_toRelativeProj {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1}
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map y ≫ s.toRelativeProj U u =
      s.toRelativeProj V v ≫
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y :
          (relativeProj (s.shrink.pointAlgebra V v)).scheme ⟶
            (relativeProj (s.shrink.pointAlgebra U u)).scheme) :=
  (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The twist `𝒪(n)` on the scheme of `V ×_X P`**, as a quasi-coherent module: the `n`-th
homogeneous piece of Tag 01NR's `⨁_n 𝒪(n)` on `Proj_V(v^*𝒜)`, read on the scheme of `V ×_X P`
through `AlgebraicGeometry.Space.RelativeProjSituation.toRelativeProj`. -/
def twistPieceQcoh (V : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj V ⟶ s.space.1) (n : ℤ) :
    (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
      (s.relativeProjPoints.fibre V v)).ringCatSheaf).FullSubcategory :=
  ⟨(Scheme.Modules.pullback (s.toRelativeProj V v)).obj
      ((Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra V v)).piece n),
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (s.toRelativeProj V v).toLRSHom.toShHom _
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra (s.shrink.pointAlgebra V v)).isQuasicoherent n)⟩

/-- The comparison of the twists `𝒪(n)` along a morphism of base changes lying over `k`, as an
isomorphism of sheaves of modules: the degree-`n` piece of
`AlgebraicGeometry.Space.RelativeProjSituation.pointTwistComparison` along the morphism of schemes
underlying `y`, transported along the square of
`AlgebraicGeometry.Space.RelativeProjSituation.toRelativeProj`. -/
def twistPieceSheafIso {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v)
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : s.relativeProjPoints.LiesOver y k) (n : ℤ) :
    @Iso (SheafOfModules.{u} ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
        (s.relativeProjPoints.fibre V v)).ringCatSheaf) _
      (quasicoherentPullbackObj s.site s.base s.containsBase y (s.twistPieceQcoh U u n)).obj
      (s.twistPieceQcoh V v n).obj :=
  pullbackSheafIsoOfSquare (s.toRelativeProj U u) (s.toRelativeProj V v)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y) (s.map_comp_toRelativeProj y)
    (gradedPieceIso (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
      (Y := (relativeProj (s.shrink.pointAlgebra V v)).scheme)
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
      (s.pointTwistComparison k u v hv ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        (s.toScheme_map_eq_of_liesOver hv hy)) n)

/-- **The comparison of the twists `𝒪(n)` along a morphism of base changes lying over `k`**:
the degree-`n` piece of `AlgebraicGeometry.Space.RelativeProjSituation.pointTwistComparison`
along the morphism of schemes underlying `y`, `y^*𝒪_{U ×_X P}(n) ≅ 𝒪_{V ×_X P}(n)`, as an
isomorphism of quasi-coherent modules. -/
def twistPieceComparison {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v)
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : s.relativeProjPoints.LiesOver y k) (n : ℤ) :
    quasicoherentPullbackObj s.site s.base s.containsBase y (s.twistPieceQcoh U u n) ≅
      s.twistPieceQcoh V v n where
  hom := ⟨(s.twistPieceSheafIso k hv y hy n).hom⟩
  inv := ⟨(s.twistPieceSheafIso k hv y hy n).inv⟩
  hom_inv_id := ObjectProperty.hom_ext _ (s.twistPieceSheafIso k hv y hy n).hom_inv_id
  inv_hom_id := ObjectProperty.hom_ext _ (s.twistPieceSheafIso k hv y hy n).inv_hom_id

/-- The underlying morphism of the comparison of the twists along a morphism lying over `k`. -/
theorem twistPieceComparison_hom_hom {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v)
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : s.relativeProjPoints.LiesOver y k) (n : ℤ) :
    (s.twistPieceComparison k hv y hy n).hom.hom =
      (pullbackSheafIsoOfSquare (s.toRelativeProj U u) (s.toRelativeProj V v)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        (s.map_comp_toRelativeProj y)
        (gradedPieceIso (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
          (Y := (relativeProj (s.shrink.pointAlgebra V v)).scheme)
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
          (s.pointTwistComparison k u v hv
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
            (s.toScheme_map_eq_of_liesOver hv hy)) n)).hom :=
  (rfl : _ = (s.twistPieceSheafIso k hv y hy n).hom).trans rfl

/-- **The cocycle of the comparisons of the twists `𝒪(n)`** (in degree `n`): along a composite
`y' ≫ y` lying over `k' ≫ k`, the comparison is the comparison along `y`, pulled back along `y'`
and contracted, followed by the comparison along `y'`. -/
theorem twistPieceComparison_comp {U V W : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1}
    {w : yoneda.obj W ⟶ s.space.1} (k : V ⟶ U) (k' : W ⟶ V)
    (hv : yoneda.map k ≫ u = v) (hw : yoneda.map k' ≫ v = w)
    (hw'' : yoneda.map (k' ≫ k) ≫ u = w)
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (y' : s.relativeProjPoints.fibre W w ⟶ s.relativeProjPoints.fibre V v)
    (hy : s.relativeProjPoints.LiesOver y k) (hy' : s.relativeProjPoints.LiesOver y' k') (n : ℤ) :
    (pullbackSheafIsoOfSquare (s.toRelativeProj U u) (s.toRelativeProj W w)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map (y' ≫ y))
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map (y' ≫ y))
        (s.map_comp_toRelativeProj (y' ≫ y))
        (gradedPieceIso (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
          (Y := (relativeProj (s.shrink.pointAlgebra W w)).scheme)
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map (y' ≫ y))
          (s.pointTwistComparison (k' ≫ k) u w hw''
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map (y' ≫ y))
            (s.toScheme_map_eq_of_liesOver hw'' (hy.comp hy'))) n)).hom =
      (Scheme.Modules.pullbackCongr
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp y' y)).hom.app
          ((Scheme.Modules.pullback (s.toRelativeProj U u)).obj
            ((Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra U u)).piece n)) ≫
      (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme s.site s.base s.containsBase).map y')
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)).inv.app
          ((Scheme.Modules.pullback (s.toRelativeProj U u)).obj
            ((Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra U u)).piece n)) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map y')).map
          (pullbackSheafIsoOfSquare (s.toRelativeProj U u) (s.toRelativeProj V v)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        (s.map_comp_toRelativeProj y)
        (gradedPieceIso (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
          (Y := (relativeProj (s.shrink.pointAlgebra V v)).scheme)
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
          (s.pointTwistComparison k u v hv
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
            (s.toScheme_map_eq_of_liesOver hv hy)) n)).hom ≫
          (pullbackSheafIsoOfSquare (s.toRelativeProj V v) (s.toRelativeProj W w)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y')
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y')
        (s.map_comp_toRelativeProj y')
        (gradedPieceIso (X := (relativeProj (s.shrink.pointAlgebra V v)).scheme)
          (Y := (relativeProj (s.shrink.pointAlgebra W w)).scheme)
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map y')
          (s.pointTwistComparison k' v w hw
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map y')
            (s.toScheme_map_eq_of_liesOver hw hy')) n)).hom := by
  have hcomp := s.pointTwistComparison_comp k u v hv
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    (s.toScheme_map_eq_of_liesOver hv hy) k' w hw hw''
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y')
    (s.toScheme_map_eq_of_liesOver hw hy')
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map (y' ≫ y))
    (s.toScheme_map_eq_of_liesOver hw'' (hy.comp hy'))
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp _ _)
    (s.toScheme_map_comp_toBase_of_liesOver hv hy)
    (s.toScheme_map_comp_toBase_of_liesOver hw hy')
  have e2 := gradedPieceIso_hom_eq_of_eq_trans _ _ _ _ n _ _ _ hcomp
  exact pullbackSheafIsoOfSquare_comp (s.toRelativeProj U u)
    (s.toRelativeProj V v) (s.toRelativeProj W w)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y')
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map (y' ≫ y))
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp _ _) _ _ _
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp _ _)
    (s.map_comp_toRelativeProj y) (s.map_comp_toRelativeProj y')
    (s.map_comp_toRelativeProj (y' ≫ y)) _ _ _ e2

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The presentation `P = P_U/P_R` of the relative Proj of Situation 0849** over a presentation
`X = U/R` of its base (`AlgebraicGeometry.Space.RelativeProjPoints.presentation`). -/
abbrev twistPresentation :
    Presentation s.site s.base s.containsBase s.relativeProjFunctor
      s.isAlgebraicSpace_relativeProjFunctor :=
  s.relativeProjPoints.presentation Px s.isAlgebraicSpace_relativeProjFunctor

/-- The target projection of the presentation lies over the target projection of the relation. -/
theorem liesOver_presentationTarget :
    s.relativeProjPoints.LiesOver (s.relativeProjPoints.presentationTarget Px) Px.target :=
  RelativeProjPoints.liesOver_fibreComparison _ _ _

/-- The source projection of the presentation lies over the source projection of the relation. -/
theorem liesOver_presentationSource :
    s.relativeProjPoints.LiesOver (s.relativeProjPoints.presentationSource Px) Px.source :=
  (RelativeProjPoints.liesOver_fibreComparison _ _ _).eqToHom_comp Px.isPullback.w

/-- The point `t ≫ u` of the relation, read through the source projection. -/
theorem map_source_comp_toSpace :
    yoneda.map Px.source ≫ Px.toSpace = RelativeProjPoints.relationPoint Px :=
  Px.isPullback.w.symm

/-- **The reindexing of a transition made of two comparisons of twists, along a morphism lying
over a morphism of test objects.**  For morphisms of base changes `t', s' : R ×_X P ⟶ U ×_X P`
lying over `kt, ks : R ⟶ U` and `x : V ×_X P ⟶ R ×_X P` lying over `xb`, the pullback along `x`
of the transition `T_{t'} ≫ T_{s'}⁻¹`, between the contractions of the pullbacks, is
`T_{x ≫ t'} ≫ T_{x ≫ s'}⁻¹`: the cocycle of the comparisons of twists at the two composites. -/
theorem schemeTransitionReindex_twistPieceComparison
    {U R V : BigFppfOver s.site s.base s.containsBase} {u : yoneda.obj U ⟶ s.space.1}
    {r : yoneda.obj R ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} (kt ks : R ⟶ U)
    (hrt : yoneda.map kt ≫ u = r) (hrs : yoneda.map ks ≫ u = r)
    (t' s' : s.relativeProjPoints.fibre R r ⟶ s.relativeProjPoints.fibre U u)
    (ht' : s.relativeProjPoints.LiesOver t' kt) (hs' : s.relativeProjPoints.LiesOver s' ks)
    (xb : V ⟶ R) (hv : yoneda.map xb ≫ r = v)
    (x : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre R r)
    (hx : s.relativeProjPoints.LiesOver x xb) (hvt : yoneda.map (xb ≫ kt) ≫ u = v)
    (hvs : yoneda.map (xb ≫ ks) ≫ u = v) (n : ℤ) :
    schemeTransitionReindex s.site s.base s.containsBase t' s' (s.twistPieceQcoh U u n)
        ((s.twistPieceComparison kt hrt t' ht' n).hom ≫
          (s.twistPieceComparison ks hrs s' hs' n).inv) x =
      (s.twistPieceComparison (xb ≫ kt) hvt (x ≫ t') (ht'.comp hx) n).hom ≫
        (s.twistPieceComparison (xb ≫ ks) hvs (x ≫ s') (hs'.comp hx) n).inv :=
  schemeTransitionReindex_eq_of_comp_of_hom_eq _ _ _ _ _ _ x _ _
    (s.twistPieceComparison xb hv x hx n) _ _ _
    (s.twistPieceComparison_hom_hom _ _ _ _ n) _
    (s.twistPieceComparison_hom_hom _ _ _ _ n) _
    (s.twistPieceComparison_hom_hom _ _ _ _ n) _
    (s.twistPieceComparison_hom_hom _ _ _ _ n) _
    (s.twistPieceComparison_hom_hom _ _ _ _ n)
    (s.twistPieceComparison_comp kt xb hrt hv hvt t' x ht' hx n)
    (s.twistPieceComparison_comp ks xb hrs hv hvs s' x hs' hx n)

/-- **The comparison of twists pulled back along `ψ`**: for `y : W₃ ×_X P ⟶ U ×_X P` lying over
`kb`, the identification `(ψ ≫ y)^*𝒪_{U ×_X P}(n) ≅ ψ^*𝒪_{W₃ ×_X P}(n)`, the contraction of the
pullbacks followed by the pullback along `ψ` of the comparison of twists along `y`. -/
def twistReindexIso {U W₃ W' : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {w₃ : yoneda.obj W₃ ⟶ s.space.1}
    (ψ : W' ⟶ s.relativeProjPoints.fibre W₃ w₃) (kb : W₃ ⟶ U) (hv : yoneda.map kb ≫ u = w₃)
    (y : s.relativeProjPoints.fibre W₃ w₃ ⟶ s.relativeProjPoints.fibre U u)
    (hy : s.relativeProjPoints.LiesOver y kb) (n : ℤ) :
    quasicoherentPullbackObj s.site s.base s.containsBase (ψ ≫ y) (s.twistPieceQcoh U u n) ≅
      quasicoherentPullbackObj s.site s.base s.containsBase ψ (s.twistPieceQcoh W₃ w₃ n) :=
  (quasicoherentPullbackCompIso s.site s.base s.containsBase ψ y (s.twistPieceQcoh U u n)).symm ≪≫
    quasicoherentPullbackMapIso s.site s.base s.containsBase ψ (s.twistPieceComparison kb hv y hy n)

/-- **The reindexing of the transition of the twists along a morphism factoring through a base
change**: along `H = ψ ≫ x` with `x` lying over `xb`, it is `Θ_{x ≫ t'} ≫ Θ_{x ≫ s'}⁻¹` for the
comparisons of twists pulled back along `ψ`. -/
theorem schemeTransitionReindex_eq_twistReindexIso
    {U R W₃ W' : BigFppfOver s.site s.base s.containsBase} {u : yoneda.obj U ⟶ s.space.1}
    {r : yoneda.obj R ⟶ s.space.1} {w₃ : yoneda.obj W₃ ⟶ s.space.1} (kt ks : R ⟶ U)
    (hrt : yoneda.map kt ≫ u = r) (hrs : yoneda.map ks ≫ u = r)
    (t' s' : s.relativeProjPoints.fibre R r ⟶ s.relativeProjPoints.fibre U u)
    (ht' : s.relativeProjPoints.LiesOver t' kt) (hs' : s.relativeProjPoints.LiesOver s' ks)
    (ψ : W' ⟶ s.relativeProjPoints.fibre W₃ w₃) (xb : W₃ ⟶ R) (hv : yoneda.map xb ≫ r = w₃)
    (x : s.relativeProjPoints.fibre W₃ w₃ ⟶ s.relativeProjPoints.fibre R r)
    (hx : s.relativeProjPoints.LiesOver x xb) (hvt : yoneda.map (xb ≫ kt) ≫ u = w₃)
    (hvs : yoneda.map (xb ≫ ks) ≫ u = w₃) (n : ℤ) (H : W' ⟶ s.relativeProjPoints.fibre R r)
    (hH : H = ψ ≫ x) (pt : H ≫ t' = ψ ≫ (x ≫ t')) (ps : H ≫ s' = ψ ≫ (x ≫ s')) :
    schemeTransitionReindex s.site s.base s.containsBase t' s' (s.twistPieceQcoh U u n)
        ((s.twistPieceComparison kt hrt t' ht' n).hom ≫
          (s.twistPieceComparison ks hrs s' hs' n).inv) H =
      eqToHom (congrArg (fun k => quasicoherentPullbackObj s.site s.base s.containsBase k
          (s.twistPieceQcoh U u n)) pt) ≫
        (s.twistReindexIso ψ (xb ≫ kt) hvt (x ≫ t') (ht'.comp hx) n).hom ≫
          (s.twistReindexIso ψ (xb ≫ ks) hvs (x ≫ s') (hs'.comp hx) n).inv ≫
            eqToHom (congrArg (fun k => quasicoherentPullbackObj s.site s.base s.containsBase k
              (s.twistPieceQcoh U u n)) ps.symm) := by
  subst hH
  rw [schemeTransitionReindex_comp, s.schemeTransitionReindex_twistPieceComparison kt ks hrt hrs
    t' s' ht' hs' xb hv x hx hvt hvs n, quasicoherentPullbackMap_comp]
  simp [twistReindexIso, quasicoherentPullbackMapIso]

section Cocycle

variable {U R W₃ W' : BigFppfOver s.site s.base s.containsBase} {u : yoneda.obj U ⟶ s.space.1}
  {r : yoneda.obj R ⟶ s.space.1} {w₃ : yoneda.obj W₃ ⟶ s.space.1} (kt ks : R ⟶ U)
  (hrt : yoneda.map kt ≫ u = r) (hrs : yoneda.map ks ≫ u = r)
  (t' s' : s.relativeProjPoints.fibre R r ⟶ s.relativeProjPoints.fibre U u)
  (ht' : s.relativeProjPoints.LiesOver t' kt) (hs' : s.relativeProjPoints.LiesOver s' ks) (n : ℤ)

/-- The indices of the comparisons of twists pulled back along `ψ`: morphisms of base changes
`W₃ ×_X P ⟶ U ×_X P` lying over a morphism of test objects compatible with the points. -/
abbrev TwistIndex (W₃ U : BigFppfOver s.site s.base s.containsBase)
    (w₃ : yoneda.obj W₃ ⟶ s.space.1) (u : yoneda.obj U ⟶ s.space.1) :=
  {p : (s.relativeProjPoints.fibre W₃ w₃ ⟶ s.relativeProjPoints.fibre U u) × (W₃ ⟶ U) //
    s.relativeProjPoints.LiesOver p.1 p.2 ∧ yoneda.map p.2 ≫ u = w₃}

/-- **The cocycle condition of the transition of the twists**, at variables: for three morphisms
`C, F₁, F₂ : W' ⟶ R ×_X P` factoring through a base change `W₃ ×_X P` by morphisms lying over
`xbC, xb₁, xb₂ : W₃ ⟶ R` with the composable-pair relations, the reindexing along `C` is the
reindexing along `F₁` followed by the reindexing along `F₂`. -/
theorem schemeTransitionReindex_cocycle (ψ : W' ⟶ s.relativeProjPoints.fibre W₃ w₃)
    (xbC xb₁ xb₂ : W₃ ⟶ R) (hvC : yoneda.map xbC ≫ r = w₃) (hv₁ : yoneda.map xb₁ ≫ r = w₃)
    (hv₂ : yoneda.map xb₂ ≫ r = w₃)
    (xC x₁ x₂ : s.relativeProjPoints.fibre W₃ w₃ ⟶ s.relativeProjPoints.fibre R r)
    (hxC : s.relativeProjPoints.LiesOver xC xbC) (hx₁ : s.relativeProjPoints.LiesOver x₁ xb₁)
    (hx₂ : s.relativeProjPoints.LiesOver x₂ xb₂)
    (b₁ : xbC ≫ kt = xb₁ ≫ kt) (b₂ : xb₁ ≫ ks = xb₂ ≫ kt) (b₃ : xb₂ ≫ ks = xbC ≫ ks)
    (C F₁ F₂ : W' ⟶ s.relativeProjPoints.fibre R r) (hC : C = ψ ≫ xC) (hF₁ : F₁ = ψ ≫ x₁)
    (hF₂ : F₂ = ψ ≫ x₂) (e₁ : C ≫ t' = F₁ ≫ t') (e₂ : F₁ ≫ s' = F₂ ≫ t')
    (e₃ : F₂ ≫ s' = C ≫ s') :
    schemeTransitionReindex s.site s.base s.containsBase t' s' (s.twistPieceQcoh U u n)
        ((s.twistPieceComparison kt hrt t' ht' n).hom ≫
          (s.twistPieceComparison ks hrs s' hs' n).inv) C =
      eqToHom (congrArg (fun k => quasicoherentPullbackObj s.site s.base s.containsBase k
          (s.twistPieceQcoh U u n)) e₁) ≫
        schemeTransitionReindex s.site s.base s.containsBase t' s' (s.twistPieceQcoh U u n)
          ((s.twistPieceComparison kt hrt t' ht' n).hom ≫
            (s.twistPieceComparison ks hrs s' hs' n).inv) F₁ ≫
          eqToHom (congrArg (fun k => quasicoherentPullbackObj s.site s.base s.containsBase k
            (s.twistPieceQcoh U u n)) e₂) ≫
            schemeTransitionReindex s.site s.base s.containsBase t' s' (s.twistPieceQcoh U u n)
              ((s.twistPieceComparison kt hrt t' ht' n).hom ≫
                (s.twistPieceComparison ks hrs s' hs' n).inv) F₂ ≫
              eqToHom (congrArg (fun k => quasicoherentPullbackObj s.site s.base s.containsBase k
                (s.twistPieceQcoh U u n)) e₃) := by
  have hp : ∀ {xb : W₃ ⟶ R} {k : R ⟶ U}, yoneda.map xb ≫ r = w₃ → yoneda.map k ≫ u = r →
      yoneda.map (xb ≫ k) ≫ u = w₃ := fun h h' => by
    rw [Functor.map_comp, Category.assoc, h', h]
  have hpt : ∀ (H : W' ⟶ s.relativeProjPoints.fibre R r)
      (x : s.relativeProjPoints.fibre W₃ w₃ ⟶ s.relativeProjPoints.fibre R r)
      (y : s.relativeProjPoints.fibre R r ⟶ s.relativeProjPoints.fibre U u)
      (_ : H = ψ ≫ x), H ≫ y = ψ ≫ (x ≫ y) := fun H x y h => by rw [h, Category.assoc]
  refine eq_eqToHom_comp_of_trivialization
    (fun k => quasicoherentPullbackObj s.site s.base s.containsBase k (s.twistPieceQcoh U u n))
    (fun p : s.TwistIndex W₃ U w₃ u => ψ ≫ p.1.1)
    (fun p => s.twistReindexIso ψ p.1.2 p.2.2 p.1.1 p.2.1 n)
    ⟨(xC ≫ t', xbC ≫ kt), ht'.comp hxC, hp hvC hrt⟩ ⟨(xC ≫ s', xbC ≫ ks), hs'.comp hxC, hp hvC hrs⟩
    ⟨(x₁ ≫ t', xb₁ ≫ kt), ht'.comp hx₁, hp hv₁ hrt⟩ ⟨(x₁ ≫ s', xb₁ ≫ ks), hs'.comp hx₁, hp hv₁ hrs⟩
    ⟨(x₂ ≫ t', xb₂ ≫ kt), ht'.comp hx₂, hp hv₂ hrt⟩ ⟨(x₂ ≫ s', xb₂ ≫ ks), hs'.comp hx₂, hp hv₂ hrs⟩
    (hpt _ _ _ hC) (hpt _ _ _ hC) (hpt _ _ _ hF₁) (hpt _ _ _ hF₁) (hpt _ _ _ hF₂) (hpt _ _ _ hF₂)
    (Subtype.ext (Prod.ext_iff.2 ⟨(ht'.comp hxC).eq (ht'.comp hx₁) b₁, b₁⟩))
    (Subtype.ext (Prod.ext_iff.2 ⟨(hs'.comp hx₁).eq (ht'.comp hx₂) b₂, b₂⟩))
    (Subtype.ext (Prod.ext_iff.2 ⟨(hs'.comp hx₂).eq (hs'.comp hxC) b₃, b₃⟩))
    e₁ e₂ e₃ _ _ _ ?_ ?_ ?_
  · exact s.schemeTransitionReindex_eq_twistReindexIso kt ks hrt hrs t' s' ht' hs' ψ xbC hvC xC hxC
      _ _ n C hC (hpt _ _ _ hC) (hpt _ _ _ hC)
  · exact s.schemeTransitionReindex_eq_twistReindexIso kt ks hrt hrs t' s' ht' hs' ψ xb₁ hv₁ x₁ hx₁
      _ _ n F₁ hF₁ (hpt _ _ _ hF₁) (hpt _ _ _ hF₁)
  · exact s.schemeTransitionReindex_eq_twistReindexIso kt ks hrt hrs t' s' ht' hs' ψ xb₂ hv₂ x₂ hx₂
      _ _ n F₂ hF₂ (hpt _ _ _ hF₂) (hpt _ _ _ hF₂)

/-- **The unit condition of the transition of the twists**, at variables: along a section
`D : U ×_X P ⟶ R ×_X P` of both projections, lying over a section of both projections of the
relation, the reindexing is the identification of its endpoints. -/
theorem schemeTransitionReindex_unit (db : U ⟶ R) (hdb : yoneda.map db ≫ r = u)
    (D : s.relativeProjPoints.fibre U u ⟶ s.relativeProjPoints.fibre R r)
    (hD : s.relativeProjPoints.LiesOver D db) (bt : db ≫ kt = 𝟙 U) (bs : db ≫ ks = 𝟙 U)
    (eDt : D ≫ t' = 𝟙 _) (eDs : D ≫ s' = 𝟙 _) :
    schemeTransitionReindex s.site s.base s.containsBase t' s' (s.twistPieceQcoh U u n)
        ((s.twistPieceComparison kt hrt t' ht' n).hom ≫
          (s.twistPieceComparison ks hrs s' hs' n).inv) D =
      eqToHom (congrArg (fun k => quasicoherentPullbackObj s.site s.base s.containsBase k
          (s.twistPieceQcoh U u n)) (eDt.trans eDs.symm)) := by
  have hp : ∀ {k : R ⟶ U}, yoneda.map k ≫ u = r → yoneda.map (db ≫ k) ≫ u = u := fun h => by
    rw [Functor.map_comp, Category.assoc, h, hdb]
  refine eq_eqToHom_of_trivialization
    (fun k => quasicoherentPullbackObj s.site s.base s.containsBase k (s.twistPieceQcoh U u n))
    (fun p : s.TwistIndex U U u u => 𝟙 _ ≫ p.1.1)
    (fun p => s.twistReindexIso (𝟙 _) p.1.2 p.2.2 p.1.1 p.2.1 n)
    ⟨(D ≫ t', db ≫ kt), ht'.comp hD, hp hrt⟩ ⟨(D ≫ s', db ≫ ks), hs'.comp hD, hp hrs⟩
    (Category.id_comp _).symm (Category.id_comp _).symm
    (Subtype.ext (Prod.ext_iff.2 ⟨eDt.trans eDs.symm, bt.trans bs.symm⟩))
    (eDt.trans eDs.symm) _ ?_
  exact s.schemeTransitionReindex_eq_twistReindexIso kt ks hrt hrs t' s' ht' hs' (𝟙 _) db hdb D hD
    _ _ n D (Category.id_comp _).symm (Category.id_comp _).symm (Category.id_comp _).symm

end Cocycle

end RelativeProjSituation

end AlgebraicGeometry.Space

end
