module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryIsoOfNatIsoOnHomotopyCategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGeometricStalkSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLerayGlobalSectionsAb
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SmallEtaleBaseChangeAbBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The composition clause of Stacks 0GIX: the base change map of a geometric fibre

Let `f : X ⟶ S` be a morphism of schemes and `s` a geometric point of `S`. Stacks 0GIX produces
two canonical maps on unbounded derived categories of abelian sheaves on the small étale sites,

`(Rf_*K)_s ⟶ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K) ⟶ RΓ(X_s, K|_{X_s})`,

and asserts in its last sentence that their composite is the usual derived base change map of the
cartesian square defining the geometric fibre. This file constructs the right-hand side of that
assertion: the two canonical maps are written in the vocabulary of
`Stacks.EtaleCohomology.smallEtalePullbackAb`, while the derived base change map of Stacks 0A2A
is written in that of `Stacks.EtaleCohomology.etaleAbelianInverseImage`.

## Main definitions

* `AlgebraicGeometry.geometricFibreDerivedBaseChangeAb` — the derived base change map
  `(Rf_*K)|_s ⟶ Rq_*(K|_{X_s})` of the cartesian square defining the geometric fibre, read in the
  vocabulary of `Stacks.EtaleCohomology.smallEtaleDerivedPullbackAb`.

## Main results

* `Stacks.CategoryTheory.conjugateEquiv_symm_id` — the canonical comparison of two left adjoints
  of one functor is the conjugate of the identity of that functor.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_eq_etaleAbelianBaseChange` — **the two underived
  étale base change comparisons of a commutative square agree**, as an equality:
  `smallEtaleBaseChangeAb` is `etaleAbelianBaseChange` conjugated by the identification of the two
  inverse images.
* `Stacks.EtaleCohomology.mapDerivedCategoryFactorsh_inv_app_comp_smallEtaleDerivedPullbackAbIso`
  — the derived identification of the two inverse images of abelian étale sheaves, read against
  the factorizations of the two degreewise actions through the homotopy category.

## Implementation notes

The two underived comparisons `Stacks.EtaleCohomology.smallEtaleBaseChangeAb` and
`Stacks.EtaleCohomology.etaleAbelianBaseChange` are the mate of one and the same comparison of
composite direct images, along adjunctions differing only in their left adjoints.
`Stacks.CategoryTheory.mateEquiv_symm_eq_whiskerLeft_whiskerRight` says that changing the left
adjoints whiskers the mate by the canonical comparisons of left adjoints, which Mathlib produces
as `CategoryTheory.conjugateEquiv` of an identity; `Stacks.CategoryTheory.conjugateEquiv_symm_id`
identifies these with `CategoryTheory.Adjunction.leftAdjointUniq`.

An equation between `Stacks.EtaleCohomology.smallEtaleBaseChangeAb` and anything built from
`Stacks.EtaleCohomology.etaleAbelianBaseChange` is type-correct only after
`Stacks.EtaleCohomology.smallEtalePushforwardAb` is unfolded to the term that
`Stacks.EtaleCohomology.etaleAbelianDirectImage` abbreviates; the coefficient categories
`Ab.{u + 1}` and `AddCommGrpCat.{max (u + 1) (u + 1)}` even resolve their `Category` instances
along different paths. Neither `rw` nor `simp only` fires on such a goal, so the proof applies
each step by `exact`, `Eq.trans` or `congrArg`, with the one reassociation stated for bare
morphisms in an abstract category.

## References

* [Stacks Project, Tag 0GIX](https://stacks.math.columbia.edu/tag/0GIX)
* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.CategoryTheory

/-- **The canonical comparison of two left adjoints of one functor is the conjugate of the
identity of that functor.** Both postcompose the unit of one of the two adjunctions to the unit of
the other, and the transpose of an adjunction is injective. -/
public theorem conjugateEquiv_symm_id {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R : D ⥤ C} (adj₁ : L₁ ⊣ R) (adj₂ : L₂ ⊣ R) :
    (conjugateEquiv adj₁ adj₂).symm (𝟙 R) = (Adjunction.leftAdjointUniq adj₂ adj₁).hom := by
  refine NatTrans.ext (funext fun c => ?_)
  refine (adj₂.homEquiv c (L₁.obj c)).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Adjunction.unit_leftAdjointUniq_hom_app adj₂ adj₁ c,
    ← unit_conjugateEquiv_symm adj₁ adj₂ (𝟙 R) c]
  simp

end Stacks.CategoryTheory

namespace Stacks.EtaleCohomology

/-! ### The two underived base change comparisons agree, as an equality -/

section Bridge

/-- Equal outer factors give equal composites of three morphisms: `a ≫ m ≫ b = a' ≫ m ≫ b'`
whenever `a = a'` and `b = b'`. -/
private theorem comp_congr₂ {C : Type*} [Category C] {A₀ A₁ A₂ A₃ : C}
    {a a' : A₀ ⟶ A₁} {m : A₁ ⟶ A₂} {b b' : A₂ ⟶ A₃} (ha : a = a') (hb : b = b') :
    a ≫ m ≫ b = a' ≫ m ≫ b' := by rw [ha, hb]

/-- The identification of the two inverse images of abelian étale sheaves, read in the other
direction, is the canonical comparison of left adjoints taken in the other order. -/
public theorem smallEtalePullbackAbIsoEtaleAbelianInverseImage_inv {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (smallEtalePullbackAbIsoEtaleAbelianInverseImage f).inv =
      (Adjunction.leftAdjointUniq (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f)
        (smallEtaleAdjunctionAb f)).hom :=
  NatTrans.ext (funext fun F => Adjunction.leftAdjointUniq_inv_app _ _ F)

variable {S T X' Y : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- **The two underived étale base change comparisons of a square agree.** For a commutative
square
```
Y --h--> X'
|e        |f'
v         v
T --g--> S
```
of schemes, `Stacks.EtaleCohomology.smallEtaleBaseChangeAb f' g h e w` is
`Stacks.EtaleCohomology.etaleAbelianBaseChange g f' e h w.symm` conjugated by the identification
`Stacks.EtaleCohomology.smallEtalePullbackAbIsoEtaleAbelianInverseImage` of the two inverse images
of abelian étale sheaves. Nothing is assumed of the square beyond commutativity. -/
public theorem smallEtaleBaseChangeAb_eq_etaleAbelianBaseChange :
    smallEtaleBaseChangeAb f' g h e w =
      Functor.whiskerLeft (smallEtalePushforwardAb g)
          (smallEtalePullbackAbIsoEtaleAbelianInverseImage f').hom ≫
        etaleAbelianBaseChange.{u, u + 1} g f' e h w.symm ≫
        Functor.whiskerRight (smallEtalePullbackAbIsoEtaleAbelianInverseImage e).inv
          (smallEtalePushforwardAb h) := by
  have e1 : (conjugateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f')
        (smallEtaleAdjunctionAb f')).symm (𝟙 (etaleAbelianDirectImage.{u, u + 1} f')) =
      (smallEtalePullbackAbIsoEtaleAbelianInverseImage f').hom :=
    Stacks.CategoryTheory.conjugateEquiv_symm_id _ _
  have e2 : (conjugateEquiv (smallEtaleAdjunctionAb e)
        (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} e)).symm
          (𝟙 (etaleAbelianDirectImage.{u, u + 1} e)) =
      (smallEtalePullbackAbIsoEtaleAbelianInverseImage e).inv :=
    (Stacks.CategoryTheory.conjugateEquiv_symm_id _ _).trans
      (smallEtalePullbackAbIsoEtaleAbelianInverseImage_inv e).symm
  have e3 := etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, u + 1} g f' e h
    w.symm (e ≫ g) rfl w.symm
  have hmate := Stacks.CategoryTheory.mateEquiv_symm_eq_whiskerLeft_whiskerRight
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} e) (smallEtaleAdjunctionAb e)
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f') (smallEtaleAdjunctionAb f')
    (TwoSquare.mk _ _ _ _
      ((etaleAbelianDirectImageCompIso'.{u, u + 1} e g (e ≫ g) rfl).hom ≫
        (etaleAbelianDirectImageCompIso'.{u, u + 1} h f' (e ≫ g) w.symm).inv))
  refine (smallEtaleBaseChangeAb_eq_mateEquiv_symm_pushforwardCompIso f' g h e w (e ≫ g) rfl
    w.symm).trans (hmate.trans ?_)
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg
    (fun t => Functor.whiskerLeft (etaleAbelianDirectImage.{u, u + 1} g)
        (smallEtalePullbackAbIsoEtaleAbelianInverseImage f').hom ≫ t ≫
      Functor.whiskerRight (smallEtalePullbackAbIsoEtaleAbelianInverseImage e).inv
        (etaleAbelianDirectImage.{u, u + 1} h)) e3.symm)
  exact comp_congr₂
    (congrArg (Functor.whiskerLeft (etaleAbelianDirectImage.{u, u + 1} g)) e1)
    (congrArg (fun z => Functor.whiskerRight z (etaleAbelianDirectImage.{u, u + 1} h)) e2)

end Bridge

/-! ### The derived identification of the two inverse images, on the image of `Qh` -/

section InverseImageQh

attribute [local instance] HasDerivedCategory.standard

/-- **The derived identification of the two inverse images of abelian étale sheaves, read on the
image of the localization of the homotopy category.** The descents of Stacks 0GIX factor through
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`, over the localization `DerivedCategory.Qh`
of the homotopy category, whereas
`Stacks.EtaleCohomology.smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage` is a lift
along the localization `DerivedCategory.Q` of the category of complexes. -/
public theorem mapDerivedCategoryFactorsh_inv_app_comp_smallEtaleDerivedPullbackAbIso
    {X Y : Scheme.{u}} (k : X ⟶ Y)
    (J : HomotopyCategory (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (.up ℤ)) :
    (smallEtalePullbackAb k).mapDerivedCategoryFactorsh.inv.app J ≫
        (smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage k).hom.app
          (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
            (smallEtalePullbackAbIsoEtaleAbelianInverseImage k).hom (.up ℤ)).app J) ≫
        (etaleAbelianInverseImage.{u, u + 1} k).mapDerivedCategoryFactorsh.inv.app J :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryFactorsh_inv_app_comp_isoOfNatIso
    _ _ (smallEtalePullbackAbIsoEtaleAbelianInverseImage k) J

end InverseImageQh

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-! ### The derived base change map of the cartesian square defining the geometric fibre -/

variable {X S : Scheme.{u}} (f : X ⟶ S) (s : GeometricPoint S)

/-- The derived base change map

`(Rf_*K)|_s ⟶ Rq_*(K|_{X_s})`

of the cartesian square defining the geometric fibre `X_s` of a morphism `f : X ⟶ S` at a
geometric point `s`, with `q : X_s ⟶ s` the structure morphism of the fibre, read in the
vocabulary of `Stacks.EtaleCohomology.smallEtaleDerivedPullbackAb`: it is
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange` conjugated by
`Stacks.EtaleCohomology.smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage`. -/
@[sga "4 XVII 4.2.12" "special case"]
public def geometricFibreDerivedBaseChangeAb :
    smallEtaleDerivedPushforwardAb f ⋙ smallEtaleDerivedPullbackAb s.hom ⟶
      smallEtaleDerivedPullbackAb (geometricFibreToSource f s) ⋙
        smallEtaleDerivedPushforwardAb (geometricFibreToPoint f s) :=
  Functor.whiskerLeft (smallEtaleDerivedPushforwardAb f)
      (smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage s.hom).hom ≫
    etaleAbelianDerivedBaseChange.{u, u + 1} f s.hom (geometricFibreToSource f s)
      (geometricFibreToPoint f s) pullback.condition ≫
    Functor.whiskerRight
      (smallEtaleDerivedPullbackAbIsoEtaleAbelianDerivedInverseImage
        (geometricFibreToSource f s)).inv
      (smallEtaleDerivedPushforwardAb (geometricFibreToPoint f s))

end AlgebraicGeometry

end
