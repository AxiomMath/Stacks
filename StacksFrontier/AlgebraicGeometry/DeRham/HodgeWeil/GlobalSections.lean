module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.DegreeZero
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Coproduct
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Algebra
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite

/-!
# `H^0_{Hodge}` and global functions, and axiom (A8) for Hodge cohomology

Let `X ⟶ S` be a morphism of schemes and let `H^q(X, Ω^p_{X/S})` be the Hodge cohomology groups.
In degree `0` they are global forms, `H^0(X, Ω^p_{X/S}) = Γ(X, Ω^p_{X/S})`, through the class map
`Stacks.HodgeWeil.hodgeSectionClass`. This identification is natural: for a commutative square

```
X' --g'--> X
|f'        |f
v          v
S' --g---> S
```

the pullback `g'^* : H^0(X, Ω^p_{X/S}) ⟶ H^0(X', Ω^p_{X'/S'})` sends the class of a global form
`ω` to the class of its pullback `g'^*ω`. For `p = 0`, where `Ω^0 = 𝒪`, it is the map
`g'^♯ : Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})` on global functions. Hence `g'^*` is bijective on
`H^0(X, Ω^0)` as soon as `g'^♯` is bijective. As the bidegrees of total degree `0` reduce to
`(0, 0)`, the same holds for the total Hodge group `H^0_{Hodge} = ⨁_{p + q = 0} H^q(Ω^p)`. For
`g' : X ⟶ Spec Γ(X, 𝒪_X)` this is axiom (A8) of Weil cohomology theories (Section 0FID) for
Hodge cohomology, in the form used in Remark 0FWE.

The target `Spec k'` of that axiom, for `k'` a finite separable algebra over a field `k`, is
étale over `k`. On a scheme `T` étale over `k`, Hodge cohomology lives in bidegree `(0, 0)`:
`Ω^p_{T/k} = 0` for `p ≥ 1`, and for `T` quasi-compact the space `T` is finite and discrete, so
`H^q(T, Ω^p_{T/k}) = 0` for `q ≠ 0`.

## Main definitions

* `Stacks.HodgeWeil.sectionCycle`: a global section of a sheaf of modules `M`, as a cocycle of
  degree `0` of the global sections of `M[0]`.

## Main results

* `Stacks.HodgeWeil.hodgeSectionClass_eq_globalCycleClass`: the class of a global form is the
  class of the corresponding global cocycle.
* `Stacks.HodgeWeil.hodgePullback_hodgeSectionClass`: **the pullback of the class of a global
  form is the class of the pulled back form.**
* `Stacks.HodgeWeil.hodgePullback_hodgeSectionClass_smul_one`: in degree `0`, the pullback is the
  map `g'^♯` on global functions.
* `Stacks.HodgeWeil.bijective_hodgePullback_zero`: `g'^*` is bijective on `H^0(X, Ω^0)` when
  `g'^♯` is bijective on global functions.
* `Stacks.HodgeWeil.bijective_hodgePiece_zero_map`: **axiom (A8) for Hodge cohomology**: the
  pullback on the total Hodge group `H^0_{Hodge}` is bijective when `g'^♯` is.
* `Stacks.HodgeWeil.isZero_hodgeCohomologyComponent_of_discreteTopology`: on a finite discrete
  scheme, `H^q(T, Ω^p) = 0` for `q ≠ 0`.
* `Stacks.HodgeWeil.isZero_hodgeCohomologyComponent_of_etale` and
  `Stacks.HodgeWeil.isZero_hodgeCohomologyComponent_of_etale_field`: for `T` étale and
  quasi-compact over a locally Artinian scheme, for instance `T` affine and étale over a field,
  `H^q(T, Ω^p_{T/k}) = 0` unless `p = q = 0`.

## Implementation notes

The class map `Stacks.HodgeWeil.hodgeSectionClass` is the class of a global form through the unit
`Γ ⟶ RΓ` of the derived global sections, in the form of
`Stacks.DerivedFunctor.singleZeroClass`; the pullback is computed on classes of global cocycles,
`Stacks.Cohomology.DerivedGlobalCupProduct.globalClass`. The two are the same map, up to the
identification of the single functor into the derived category with the single functor into the
homotopy category followed by the localization (`hodgeSectionClass_eq_globalCycleClass`).

The vanishing in positive degrees on a finite discrete scheme does not go through the vanishing
of cohomology of quasi-coherent sheaves on affine schemes (Tag 01XB): a finite discrete scheme
is the disjoint union of its points, Hodge cohomology splits along a decomposition into open and
closed pieces (`Stacks.HodgeWeil.bijective_hodgePullback_prod_of_disjoint`), and global sections
are exact on a one-point space. The argument is an induction on the number of points.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Tag 03WS](https://stacks.math.columbia.edu/tag/03WS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent deRhamTerm baseRingedSpace)
open Stacks.Cohomology.DerivedSectionsLeray (sectionsOverOpen derivedSectionsOverOpen
  derivedSectionsOverOpenUnit sectionsUnitQ)
open Stacks.Cohomology.DerivedGlobalCupProduct (globalCycleClass sectionsComplex globalSections)
open Stacks.Cohomology.GlobalKunneth (baseRing)
open Stacks.DeRhamDirectImage (inverseImageBase)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

/-! ### The class of a global form as the class of a global cocycle -/

section RingedSpace

/-- **A global section as a global cocycle**: a global section of a sheaf of modules `M` on a
ringed space `Z` is a cocycle of degree `0` of the complex `Γ(Z, M[0])` of global sections of `M`
placed in degree `0`. -/
def sectionCycle (Z : RingedSpace.{u, u}) (M : _root_.SheafOfModules.{u} (structureSheafRing Z)) :
    (sectionsOverOpen Z ⊤).obj M ⟶
      (sectionsComplex Z ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)).cycles 0 :=
  (((sectionsOverOpen Z ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj M)).liftCycles
    ((sectionsOverOpen Z ⊤).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv) 1
      (by simp) (Stacks.DerivedFunctor.singleZeroClass_d _ _)

/-- The cocycle of a global section is the section, placed in degree `0`. -/
theorem iCycles_sectionCycle (Z : RingedSpace.{u, u})
    (M : _root_.SheafOfModules.{u} (structureSheafRing Z)) (x : (sectionsOverOpen Z ⊤).obj M) :
    ((sectionsComplex Z ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)).iCycles
        0).hom ((sectionCycle Z M).hom x) =
      ((sectionsOverOpen Z ⊤).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv).hom x :=
  ConcreteCategory.congr_hom (HomologicalComplex.liftCycles_i _ _ _ _ _) x

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier)
    (AlgebraicGeometry.SheafOfModules.moduleOfDifferentials.{u, u, u} φ))

/-- `iCycles_sectionCycle` for the sheaf of `p`-forms. -/
private theorem iCycles_sectionCycle_deRhamTerm (p : ℕ) (x : globalForms B p) :
    ((sectionsComplex (baseRingedSpace A) ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (deRhamTerm (X := X) B p))).iCycles 0).hom
        ((sectionCycle (baseRingedSpace A) (deRhamTerm (X := X) B p)).hom x) =
      ((sectionsOverOpen (baseRingedSpace A) ⊤).map (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ) 0 (deRhamTerm (X := X) B p)).inv).hom x :=
  iCycles_sectionCycle _ _ x

/-- **The class of a global form is the class of its global cocycle**: `hodgeSectionClass`
agrees with the class `globalCycleClass` in `H^0(X, Ω^p)` of the cocycle `sectionCycle` of the
form, for the ringed space `(X, A)`. -/
theorem hodgeSectionClass_eq_globalCycleClass (p : ℕ) :
    hodgeSectionClass B p = globalCycleClass (S := baseRingedSpace A)
      (K := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (deRhamTerm (X := X) B p))
      (i := 0) (sectionCycle (baseRingedSpace A) (deRhamTerm (X := X) B p)) := by
  let M := deRhamTerm (X := X) B p
  let N := (HomologicalComplex.single
    (_root_.SheafOfModules.{u} (structureSheafRing (baseRingedSpace A))) (ComplexShape.up ℤ)
      0).obj M
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A))) 0
  have key : (DerivedCategory.singleFunctorIsoCompQh
      (_root_.SheafOfModules.{u} (structureSheafRing (baseRingedSpace A))) 0).inv.app M =
      (DerivedCategory.quotientCompQhIso
        (_root_.SheafOfModules.{u} (structureSheafRing (baseRingedSpace A)))).hom.app N :=
    Category.id_comp _
  refine Eq.trans (b := RingTheory.TorProducts.cycleClass
    (R := (baseRing (baseRingedSpace A) : Type u)) (sectionCycle (baseRingedSpace A) M) ≫
    H.map ((DerivedCategory.quotientCompQhIso
        (ModuleCat.{u} (baseRing (baseRingedSpace A)))).inv.app _) ≫
    H.map ((derivedSectionsOverOpenUnit (baseRingedSpace A) ⊤).app
          ((HomotopyCategory.quotient _ _).obj N)) ≫
    H.map ((derivedSectionsOverOpen (baseRingedSpace A) ⊤).map
          ((DerivedCategory.singleFunctorIsoCompQh
            (_root_.SheafOfModules.{u} (structureSheafRing (baseRingedSpace A))) 0).inv.app M)))
    rfl ?_
  rw [key]
  refine congrArg (RingTheory.TorProducts.cycleClass
    (R := (baseRing (baseRingedSpace A) : Type u)) (sectionCycle (baseRingedSpace A) M) ≫ ·) ?_
  exact ((H.map_comp _ _).trans (congrArg (H.map _ ≫ ·) (H.map_comp _ _))).symm

end RingedSpace

/-! ### Naturality of the class of a global form -/

section Square

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- **The pullback of the class of a global form is the class of the pulled back form**: for a
commutative square, `g'^*[ω] = [g'^*ω]` in `H^0(X', Ω^p_{X'/S'})` for every global `p`-form `ω`
on `X`. -/
theorem hodgePullback_hodgeSectionClass (p : ℕ)
    (x : globalForms (Scheme.Hom.deRhamAlgebras f) p) :
    hodgePullback g' f' f g w p 0 (hodgeSectionClass (Scheme.Hom.deRhamAlgebras f) p x) =
      hodgeSectionClass (Scheme.Hom.deRhamAlgebras f') p
        (Scheme.Hom.relativeDifferentialFormsPullback g' f f' g w (p : ℤ) ⊤ x) := by
  rw [hodgeSectionClass_eq_globalCycleClass, hodgeSectionClass_eq_globalCycleClass]
  refine cohomologyPullback_globalClass _ _ 0 _ _ ?_
  refine (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (((globalSections (inverseImageBase f)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (formsSinglePushforward g' f' f g w p)) 0) _).trans ?_
  refine (congrArg (fun y => ((((globalSections (inverseImageBase f)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (formsSinglePushforward g' f' f g w p)).f 0).hom y)
      (iCycles_sectionCycle_deRhamTerm _ p x)).trans ?_
  refine (formsSinglePushforward_f_zero_val_app g' f' f g w p (op ⊤)
    (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      ((Scheme.Hom.deRhamComplex f).X p)).inv.val.app (op ⊤)).hom x)).trans ?_
  refine Eq.trans ?_ (iCycles_sectionCycle_deRhamTerm (Scheme.Hom.deRhamAlgebras f') p
    (Scheme.Hom.relativeDifferentialFormsPullback g' f f' g w (p : ℤ) ⊤ x)).symm
  rfl

/-- **In degree `0` the pullback is the map on global functions**: `g'^*` sends the class of the
function `r ∈ Γ(X, 𝒪_X)`, the form `r · 1`, to the class of `g'^♯(r) · 1`. -/
theorem hodgePullback_hodgeSectionClass_smul_one (r : X.sheaf.obj.obj (op ⊤)) :
    hodgePullback g' f' f g w 0 0 (hodgeSectionClass (Scheme.Hom.deRhamAlgebras f) 0
      (show globalForms (Scheme.Hom.deRhamAlgebras f) 0 from
        r • (Scheme.Hom.deRhamAlgebras f).exterior.one.eval (op ⊤))) =
      hodgeSectionClass (Scheme.Hom.deRhamAlgebras f') 0
        (show globalForms (Scheme.Hom.deRhamAlgebras f') 0 from
          (show X'.sheaf.obj.obj (op ⊤) from (g'.app ⊤).hom r) •
            (Scheme.Hom.deRhamAlgebras f').exterior.one.eval (op ⊤)) := by
  refine (hodgePullback_hodgeSectionClass g' f' f g w 0 _).trans (congrArg _ ?_)
  refine (Scheme.Hom.relativeDifferentialFormsPullback_smul g' f f' g w 0 ⊤ r _).trans ?_
  exact congrArg (_ • ·) (Scheme.Hom.relativeDifferentialFormsPullback_one g' f f' g w ⊤)

/-- **The pullback is bijective on `H^0(X, Ω^0)` when `g'^♯` is bijective on global
functions**: both groups are the global functions, and the pullback is `g'^♯`. -/
theorem bijective_hodgePullback_zero (h : Function.Bijective (g'.app ⊤).hom) :
    Function.Bijective (hodgePullback g' f' f g w 0 0) := by
  exact (Function.Bijective.of_comp_iff _
    (bijective_hodgeSectionClass_smul_one (Scheme.Hom.deRhamAlgebras f))).1
    ((congrArg Function.Bijective
      (funext (hodgePullback_hodgeSectionClass_smul_one g' f' f g w))).mpr
      ((bijective_hodgeSectionClass_smul_one (Scheme.Hom.deRhamAlgebras f')).comp h))

/-- **The axiom (A8) for Hodge cohomology** (Section 0FID, Remark 0FWE): the pullback
`H^0_{Hodge}(X/S) ⟶ H^0_{Hodge}(X'/S')` on the total Hodge groups of degree `0`, summand by
summand, is bijective when `g'^♯ : Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})` is bijective. The only bidegree of
total degree `0` is `(0, 0)`. For `X' ⟶ X = Spec Γ(X', 𝒪_{X'})` this is the condition that
`H^0(Spec k') ⟶ H^0(X')` be an isomorphism for `k' = Γ(X', 𝒪_{X'})`. -/
theorem bijective_hodgePiece_zero_map (h : Function.Bijective (g'.app ⊤).hom) :
    Function.Bijective (DirectSum.map fun i : HodgeBidegreeInt 0 =>
      (hodgePullback g' f' f g w i.1.1 (i.1.2 : ℤ)).toAddMonoidHom) := by
  have hi : ∀ i : HodgeBidegreeInt 0,
      Function.Bijective (hodgePullback g' f' f g w i.1.1 (i.1.2 : ℤ)) := by
    rintro ⟨⟨p, q⟩, hpq⟩
    obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by omega
    exact bijective_hodgePullback_zero g' f' f g w h
  exact ⟨(DirectSum.map_injective _).2 fun i => (hi i).1,
    (DirectSum.map_surjective _).2 fun i => (hi i).2⟩

end Square

/-! ### Hodge cohomology of a scheme étale over a field -/

section Etale

/-- The induction behind `isZero_hodgeCohomologyComponent_of_discreteTopology`, on the number
`n` of points. -/
private theorem isZero_hodgeCohomologyComponent_of_card_eq {S : Scheme.{u}} (n : ℕ) :
    ∀ {Z : Scheme.{u}} (f : Z ⟶ S) [Finite Z] [DiscreteTopology Z], Nat.card Z = n →
      ∀ (p : ℕ) {q : ℤ}, q ≠ 0 →
        IsZero (hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Z f _ _ hn p q hq
  by_cases hZ : Subsingleton Z
  · exact isZero_hodgeCohomologyComponent_of_subsingleton _ p hq
  obtain ⟨x, -⟩ : ∃ x y : Z, x ≠ y := by
    by_contra hc
    push Not at hc
    exact hZ ⟨hc⟩
  let U : Z.Opens := ⟨{x}, isOpen_discrete _⟩
  let V : Z.Opens := ⟨{x}ᶜ, isOpen_discrete _⟩
  have hdisj : U ⊓ V = ⊥ := by
    ext y
    simp [U, V]
  have hcov : U ⊔ V = ⊤ := by
    ext y
    simp [U, V]
  have h := bijective_hodgePullback_prod_of_disjoint f hdisj hcov p q
  have : Subsingleton U := inferInstanceAs (Subsingleton ({x} : Set Z))
  have : Finite V := inferInstanceAs (Finite ({x}ᶜ : Set Z))
  have : DiscreteTopology V := inferInstanceAs (DiscreteTopology ({x}ᶜ : Set Z))
  have hU : IsZero (hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras (U.ι ≫ f)) p q) :=
    isZero_hodgeCohomologyComponent_of_subsingleton _ p hq
  have hV : IsZero (hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras (V.ι ≫ f)) p q) :=
    ih (Nat.card V) (hn ▸ Finite.card_subtype_lt (p := fun y => y ∈ V) (x := x) (by simp [V]))
      (V.ι ≫ f) rfl p hq
  have := ModuleCat.isZero_iff_subsingleton.mp hU
  have := ModuleCat.isZero_iff_subsingleton.mp hV
  have : Subsingleton (hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q) :=
    ⟨fun a b => h.1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- **Hodge cohomology of a finite discrete scheme vanishes in nonzero degrees**: for `Z` finite
and discrete over `S`, `H^q(Z, Ω^p_{Z/S}) = 0` for `q ≠ 0`. The scheme is the disjoint union of
its points, Hodge cohomology splits along it, and on a point global sections are exact. -/
theorem isZero_hodgeCohomologyComponent_of_discreteTopology {Z S : Scheme.{u}} (f : Z ⟶ S)
    [Finite Z] [DiscreteTopology Z] (p : ℕ) {q : ℤ} (hq : q ≠ 0) :
    IsZero (hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q) :=
  isZero_hodgeCohomologyComponent_of_card_eq _ f rfl p hq

/-- **Hodge cohomology of a quasi-compact étale scheme over a locally Artinian base lives in
bidegree `(0, 0)`**: `H^q(T, Ω^p_{T/S}) = 0` unless `p = q = 0`. The morphism is smooth of
relative dimension `0`, so `Ω^p_{T/S} = 0` for `p ≥ 1`; it is locally quasi-finite (Tag 03WS),
so `T` is locally Artinian, hence discrete, and finite since it is quasi-compact. -/
theorem isZero_hodgeCohomologyComponent_of_etale {T S : Scheme.{u}} (f : T ⟶ S)
    [IsLocallyArtinian S] [Etale f] [CompactSpace T] {p : ℕ} {q : ℤ} (h : p ≠ 0 ∨ q ≠ 0) :
    IsZero (hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q) := by
  rcases h with hp | hq
  · exact isZero_hodgeCohomologyComponent_of_smoothOfRelativeDimension f 0
      (Nat.pos_of_ne_zero hp) q
  · have := (locallyQuasiFinite_of_etale f).2
    have : IsLocallyArtinian T := .of_locallyQuasiFinite f
    have : IsArtinianScheme T := ⟨⟩
    exact isZero_hodgeCohomologyComponent_of_discreteTopology f p hq

/-- **Hodge cohomology of an affine scheme étale over a field lives in bidegree `(0, 0)`**: for
`T` affine and étale over a field `k`, for instance `T = Spec k'` with `k'` a finite separable
`k`-algebra, `H^q(T, Ω^p_{T/k}) = 0` unless `p = q = 0`. -/
theorem isZero_hodgeCohomologyComponent_of_etale_field {k : Type u} [Field k] {T : Scheme.{u}}
    (f : T ⟶ Spec (CommRingCat.of k)) [Etale f] [IsAffine T] {p : ℕ} {q : ℤ}
    (h : p ≠ 0 ∨ q ≠ 0) :
    IsZero (hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q) := by
  have : IsLocallyArtinian (Spec (CommRingCat.of k)) := by
    rw [Scheme.isLocallyArtinianScheme_Spec]
    infer_instance
  exact isZero_hodgeCohomologyComponent_of_etale f h

end Etale

end Stacks.HodgeWeil

end
