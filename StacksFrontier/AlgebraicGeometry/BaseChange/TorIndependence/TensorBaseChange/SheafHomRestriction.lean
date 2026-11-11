module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PointwiseRestrictionConverse
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkCohomologyMapTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BaseChangeComparisonMaps
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackLocality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackStrictlyPerfect

/-!
# The comparison for a derived internal hom restricts to opens

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes, `E, K ∈ D(𝒪_X)`, `K' ∈ D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'`.
For an open `U ⊆ X`, with inclusions `j : U ⟶ X` and `j' : g'⁻¹(U) ⟶ X'`, the square restricts
to the cartesian square `g'⁻¹(U) → U → S ← S'` and the datum `(K, K', φ)` to the datum
`(Lj^*K, L(j')^*K', φ_U)` of `Stacks.Cohomology.BaseChangeCover.pullDatum`.  Two data on the
restricted square are then attached to `R𝓗om(E, K)`: the restriction of the comparison
`L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')`, and the comparison for `Lj^*E`, `Lj^*K`, `L(j')^*K'`
and `φ_U`.  The map of Tag 08I3 along an open immersion is an isomorphism for arbitrary objects,
so these two data are isomorphic, and the map of Stacks 0DJ7 is invertible for one exactly when
it is for the other.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.map_derivedPullbackSheafHomMap_comp_map`:
  Tag 08I3 along a composite, followed by a map in the second variable.
* `map_derivedPullbackSheafHomMap_comp_baseChangeSheafHomComparison_pullDatum`, in the namespace
  `Stacks.Cohomology.BaseChangeCover`: for a commutative square of ringed spaces, the
  comparison at the pulled-back datum, preceded by Tag 08I3 along the right side, is the
  pulled-back comparison followed by Tag 08I3 along the left side.
* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_pullDatum_baseChangeSheafHomComparison_iff`:
  the map of Stacks 0DJ7 at the two data on the restricted square is invertible for one exactly
  when it is for the other.

## Implementation notes

The objects of `D(𝒪_X)` are written at three spellings of the category of `𝒪_X`-modules (the one
of the derived pullback, the one of the derived internal hom, and the one of the derived tensor
product), equal by unfolding but not syntactically.  The diagram chases are therefore made by
lemmas over an arbitrary category and instantiated by unification, not by rewriting.  The
transport along the commutativity `gZ ≫ j = j' ≫ g'` is identified with the identity through
heterogeneous equality, so that the transport isomorphisms are the ones the composition
isomorphism `Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` is built from.

## References

* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace Stacks.Cohomology.DerivedInternalHomPullback

open _root_.AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y Z : RingedSpace.{u, u}}

private theorem chase_comp {C : Type*} [Category C] {S₀ S₁ W₀ W W₂ V R T₁ : C}
    (x₁ : S₀ ⟶ W₀) (x₂ : W₀ ⟶ W) (Hz : W ⟶ T₁) (μh : S₀ ⟶ S₁) (μi : S₁ ⟶ S₀) (νP : S₁ ⟶ V)
    (a : W ⟶ W₂) (b : W₂ ⟶ V) (c : V ⟶ R) (d : R ⟶ T₁) (Hb : W₂ ⟶ R) (a' : T₁ ⟶ R)
    (h₁ : νP = μi ≫ (x₁ ≫ x₂) ≫ a ≫ b) (hμ : μh ≫ μi = 𝟙 _) (hbc : b ≫ c = Hb)
    (hnat : a ≫ Hb = Hz ≫ a') (had : a' ≫ d = 𝟙 _) :
    x₁ ≫ x₂ ≫ Hz = μh ≫ νP ≫ c ≫ d := by
  subst h₁
  simp only [Category.assoc, reassoc_of% hμ, reassoc_of% hbc, reassoc_of% hnat, had,
    Category.comp_id]

/-- **Tag 08I3 along a composite, followed by a map in the second variable.**  The derived
pullback along `f` of the canonical map along `g`, followed by the canonical map along `f` and by
`R𝓗om(Lf^*Lg^*E, z)`, is the canonical map along `f ≫ g` read through the composition
isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Stacks 0D5S. -/
theorem map_derivedPullbackSheafHomMap_comp_map (f : X ⟶ Y) (g : Y ⟶ Z)
    (E K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z))
    {T : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)}
    (z : (derivedPullback f).obj ((derivedPullback g).obj K) ⟶ T) :
    (derivedPullback f).map (derivedPullbackSheafHomMap g E K) ≫
        derivedPullbackSheafHomMap f ((derivedPullback g).obj E) ((derivedPullback g).obj K) ≫
        ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
          (op ((derivedPullback f).obj ((derivedPullback g).obj E)))).map z =
      (derivedPullbackCompIsoCanonical f g).hom.app _ ≫ derivedPullbackSheafHomMap (f ≫ g) E K ≫
        ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
          (op ((derivedPullback (f ≫ g)).obj E))).map
            ((derivedPullbackCompIsoCanonical f g).inv.app K ≫ z) ≫
        ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map
          ((derivedPullbackCompIsoCanonical f g).hom.app E).op).app T :=
  chase_comp _ _ _ _ _ _ _ _ _ _ _ _ (derivedPullbackSheafHomMap_comp f g E K)
    (Iso.hom_inv_id_app _ _)
    (((((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
      (op ((derivedPullback (f ≫ g)).obj E)))).map_comp _ _).symm.trans
        (congrArg ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
          (op ((derivedPullback (f ≫ g)).obj E))).map (Iso.hom_inv_id_app_assoc _ _ _)))
    (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map
      ((derivedPullbackCompIsoCanonical f g).inv.app E).op).naturality z).symm
    (Iso.inv_hom_id_app ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).mapIso
      ((derivedPullbackCompIsoCanonical f g).app E).op) T)

private theorem chase_refl {C : Type*} [Category C] {P V V' : C} (ν : P ⟶ V) (m m' : V ⟶ V')
    (i : P ⟶ P) (k : V' ⟶ V') (hm : m = m') (hi : i = 𝟙 P) (hk : k = 𝟙 V') :
    ν ≫ m = i ≫ ν ≫ m' ≫ k := by
  subst hm hi hk
  simp only [Category.id_comp, Category.comp_id]

/-- **Tag 08I3 along equal morphisms.**  For `e : b = a` and maps `εK`, `εH`, `εE` from the
derived pullbacks along `a` to those along `b` which are identities up to the equation, the
canonical map along `a` followed by a map in the second variable through `εK` is `εH` followed
by the canonical map along `b`. -/
theorem derivedPullbackSheafHomMap_comp_map_of_heq {a b : X ⟶ Y} (e : b = a)
    (E K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    {T : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)}
    (y : (derivedPullback b).obj K ⟶ T)
    (εK : (derivedPullback a).obj K ⟶ (derivedPullback b).obj K)
    (εH : (derivedPullback a).obj
        (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op E)).obj K) ⟶
      (derivedPullback b).obj (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op E)).obj K))
    (εE : (derivedPullback a).obj E ⟶ (derivedPullback b).obj E)
    (hK : εK ≍ 𝟙 ((derivedPullback a).obj K))
    (hH : εH ≍ 𝟙 ((derivedPullback a).obj
      (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj (op E)).obj K)))
    (hE : εE ≍ 𝟙 ((derivedPullback a).obj E)) :
    derivedPullbackSheafHomMap a E K ≫
        ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
          (op ((derivedPullback a).obj E))).map (εK ≫ y) =
      εH ≫ derivedPullbackSheafHomMap b E K ≫
        ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
          (op ((derivedPullback b).obj E))).map y ≫
        ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map εE.op).app T := by
  subst e
  subst hK hH hE
  exact chase_refl _ _ _ _ _
    (congrArg ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
      (op ((derivedPullback b).obj E))).map (Category.id_comp y)) rfl
    ((congrArg (fun t => NatTrans.app t T)
      ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map_id _)).trans (NatTrans.id_app _ _))

end Stacks.Cohomology.DerivedInternalHomPullback

namespace Stacks.Cohomology.BaseChangeCover

open _root_.AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedInternalHomPullback Stacks.Cohomology.DerivedBaseChange
open Stacks.Cohomology.DerivedBaseChangeComparison
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

private theorem chase_square {C : Type*} [Category C]
    {A₀ B₀ B₁ T₁ A₁ V R A₂ V' R' A₃ A₄ B₄ A₅ B₅ : C}
    (x₁ : A₀ ⟶ B₀) (x₂ : B₀ ⟶ B₁) (m₁ : B₁ ⟶ T₁)
    (u₁ : A₀ ⟶ A₁) (νP : A₁ ⟶ V) (cP : V ⟶ R) (d₁ : R ⟶ T₁) (cP' : V ⟶ R)
    (εH : A₁ ⟶ A₂) (νQ : A₂ ⟶ V') (cQ : V' ⟶ R') (eE : R' ⟶ R)
    (lH : A₁ ⟶ A₃) (Lc : A₃ ⟶ A₄) (νj : A₄ ⟶ B₄) (Hα : B₄ ⟶ T₁)
    (μi : A₂ ⟶ A₃) (μh : A₃ ⟶ A₂) (Lν : A₃ ⟶ A₅) (LHφ : A₅ ⟶ A₄) (νj' : A₅ ⟶ B₅)
    (HLφ : B₅ ⟶ B₄) (dE : R' ⟶ B₄)
    (hA₁ : x₁ ≫ x₂ ≫ m₁ = u₁ ≫ νP ≫ cP ≫ d₁) (hc : cP = cP')
    (hB : νP ≫ cP' = εH ≫ νQ ≫ cQ ≫ eE)
    (hl : lH = εH ≫ μi) (hLc : Lc = Lν ≫ LHφ) (hnt : LHφ ≫ νj = νj' ≫ HLφ)
    (hA₂ : Lν ≫ νj' ≫ HLφ = μh ≫ νQ ≫ cQ ≫ dE) (hμ : μi ≫ μh = 𝟙 _)
    (hE : dE ≫ Hα = eE ≫ d₁) :
    x₁ ≫ x₂ ≫ m₁ = (u₁ ≫ lH ≫ Lc) ≫ νj ≫ Hα := by
  subst hc hl hLc
  rw [hA₁]
  simp only [Category.assoc, reassoc_of% hnt, reassoc_of% hA₂, reassoc_of% hμ, hE,
    reassoc_of% hB]

private theorem map_op_app_chase {C D D' : Type*} [Category C] [Category D] [Category D']
    (H : Cᵒᵖ ⥤ D ⥤ D') {p q r s : C} (m₁ : p ⟶ q) (l : q ⟶ s) (ε : q ⟶ r) (μi : r ⟶ s)
    (μh : s ⟶ r) (hl : l = ε ≫ μi) (hμ : μi ≫ μh = 𝟙 r) (T : D) :
    (H.map μh.op).app T ≫ (H.map (m₁ ≫ l).op).app T =
      (H.map ε.op).app T ≫ (H.map m₁.op).app T := by
  subst hl
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← H.map_comp, ← H.map_comp, ← op_comp,
    ← op_comp, Category.assoc, Category.assoc, hμ, Category.comp_id]

variable {Z' Z X' X : RingedSpace.{u, u}} (gZ : Z' ⟶ Z) (j' : Z' ⟶ X') (j : Z ⟶ X)
  (g' : X' ⟶ X) (w : gZ ≫ j = j' ≫ g')

/-- **Pulling back the comparison for a derived internal hom along a square.**  For a
commutative square `gZ ≫ j = j' ≫ g'` of ringed spaces, the comparison
`L(gZ)^*R𝓗om(Lj^*E, Lj^*K) ⟶ R𝓗om(L(gZ)^*Lj^*E, L(j')^*K')` at the pulled-back datum, preceded
by the derived pullback of Tag 08I3 along `j`, is the pulled-back datum of the comparison along
`g'` followed by Tag 08I3 along `j'` and the identification
`L(gZ)^*Lj^*E ≅ L(j')^*L(g')^*E` in the first variable. -/
theorem map_derivedPullbackSheafHomMap_comp_baseChangeSheafHomComparison_pullDatum
    (E K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
    (K' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X'))
    (φ : (derivedPullback g').obj K ⟶ K') :
    (derivedPullback gZ).map (derivedPullbackSheafHomMap j E K) ≫
        baseChangeSheafHomComparison gZ ((derivedPullback j).obj E) ((derivedPullback j).obj K)
          ((derivedPullback j').obj K') (pullDatum gZ j' j g' w K K' φ) =
      pullDatum gZ j' j g' w (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op E)).obj K)
          (((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
            (op ((derivedPullback g').obj E))).obj K')
          (baseChangeSheafHomComparison g' E K K' φ) ≫
        derivedPullbackSheafHomMap j' ((derivedPullback g').obj E) K' ≫
        ((Stacks.SheafOfModules.derivedSheafHom Z'.sheaf).map
          ((derivedPullbackCompIsoCanonical gZ j).hom.app E ≫
            (derivedPullbackCompIsoLeft gZ j' j g' w).inv.app E).op).app
          ((derivedPullback j').obj K') := by
  have hA₁ := map_derivedPullbackSheafHomMap_comp_map gZ j E K (pullDatum gZ j' j g' w K K' φ)
  have hB := derivedPullbackSheafHomMap_comp_map_of_heq w.symm E K
    ((derivedPullbackCompIsoCanonical j' g').inv.app K ≫ (derivedPullback j').map φ) _ _ _
    ((heq_of_eq (eqToIso_derivedPullback_inv_app' w.symm K)).trans (eqToHom_heq_id_dom _ _ _))
    ((heq_of_eq (eqToIso_derivedPullback_inv_app' w.symm
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op E)).obj K))).trans
        (eqToHom_heq_id_dom _ _ _))
    ((heq_of_eq (eqToIso_derivedPullback_inv_app' w.symm E)).trans (eqToHom_heq_id_dom _ _ _))
  have hl := derivedPullbackCompIsoLeft_inv_app g' j j' gZ w
    (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op E)).obj K)
  have hnt := derivedPullbackSheafHomMap_naturality_target j' ((derivedPullback g').obj E) φ
  have hA₂ := map_derivedPullbackSheafHomMap_comp_map j' g' E K ((derivedPullback j').map φ)
  have hE := map_op_app_chase (Stacks.SheafOfModules.derivedSheafHom Z'.sheaf)
    ((derivedPullbackCompIsoCanonical gZ j).hom.app E) _ _ _
    ((derivedPullbackCompIsoCanonical j' g').hom.app E)
    (derivedPullbackCompIsoLeft_inv_app g' j j' gZ w E)
    (Iso.inv_hom_id_app (derivedPullbackCompIsoCanonical j' g') E)
    ((derivedPullback j').obj K')
  unfold baseChangeSheafHomComparison
  unfold pullDatum at hA₁ ⊢
  exact chase_square _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA₁
    (congrArg ((Stacks.SheafOfModules.derivedSheafHom Z'.sheaf).obj
        (op ((derivedPullback (gZ ≫ j)).obj E))).map
      ((Iso.inv_hom_id_app_assoc _ _ _).trans
        ((congrArg (· ≫ (derivedPullback j').map φ)
          (derivedPullbackCompIsoLeft_inv_app g' j j' gZ w K)).trans (Category.assoc _ _ _))))
    hB hl ((derivedPullback j').map_comp _ _) hnt hA₂ (Iso.inv_hom_id_app _ _) hE

end Stacks.Cohomology.BaseChangeCover


namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedInternalHomPullback
open Stacks.Cohomology.DerivedBaseChange Stacks.Cohomology.BaseChangeCover
open Stacks.Cohomology.DerivedBaseChangeComparison
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

section

attribute [local instance] hasDerivedCategory_ringedSpaceModules

/-- `AlgebraicGeometry.isIso_baseChangeCohomologyMap_iff_of_isIso_source` for a datum given as
any map equal to `L(g')^*θ ≫ φ`. -/
private theorem isIso_baseChangeCohomologyMap_iff_of_eq_map_comp (f : X ⟶ S) (g : S' ⟶ S)
    (f' : X' ⟶ S') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} X'.Modules]
    (K₁ K₂ : DerivedCategory X.Modules)
    (K' : DerivedCategory X'.Modules) (θ : K₁ ⟶ K₂) (hθ : IsIso θ)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K₂ ⟶ K')
    (χ : (derivedPullback g'.toLRSHom.toShHom).obj K₁ ⟶ K')
    (hχ : χ = (derivedPullback g'.toLRSHom.toShHom).map θ ≫ φ) (x' : X')
    [HasDerivedCategory.{w} (ModuleCat.{u} (S.presheaf.stalk (f (g' x'))))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk (g' x')))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (S'.presheaf.stalk (f' x')))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (X'.presheaf.stalk x'))]
    (n : ℤ) :
    IsIso (baseChangeCohomologyMap f g f' g' w K₁ K' χ x' n) ↔
      IsIso (baseChangeCohomologyMap f g f' g' w K₂ K' φ x' n) := by
  subst hχ
  exact isIso_baseChangeCohomologyMap_iff_of_isIso_source f g f' g' w K₁ K₂ K' θ hθ φ x' n

end

attribute [local instance] HasDerivedCategory.standard

/-- **Tag 08I3 along the inclusion of an open subscheme is an isomorphism.** -/
theorem isIso_derivedPullbackSheafHomMap_opensι (U : X.Opens)
    (E K : DerivedCategory X.Modules) :
    IsIso (derivedPullbackSheafHomMap U.ι.toLRSHom.toShHom E K) :=
  Stacks.Cohomology.DerivedOpenImmersion.isIso_derivedPullbackSheafHomMap_ofRestrict
    X.toRingedSpace U E K

/-- **Condition (1) of Stacks 0DJ8 for a derived internal hom commutes with restriction to an
open.**  For a cartesian square `X' → X → S ← S'`, an open `U ⊆ X` and the restricted cartesian
square `g'⁻¹(U) → U → S ← S'`, the map of Stacks 0DJ7 at the restriction of the comparison
`L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')` is invertible at `y` in degree `n` exactly when the
one at the comparison for the restricted objects `Lj^*E`, `Lj^*K`, `L(j')^*K'` and the
restricted datum is.  Nothing is assumed of `E`, `K`, `K'` or `φ`: the canonical maps of Tag 08I3
along the open immersions `j` and `j'` are isomorphisms. -/
theorem isIso_baseChangeCohomologyMap_pullDatum_baseChangeSheafHomComparison_iff
    (hpb : IsPullback g' f' f g) (U : X.Opens) (E K : DerivedCategory X.Modules)
    (K' : DerivedCategory X'.Modules) (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (y : (g' ⁻¹ᵁ U).toScheme) (n : ℤ) :
    IsIso (baseChangeCohomologyMap (U.ι ≫ f) g ((g' ⁻¹ᵁ U).ι ≫ f') (g' ∣_ U)
      ((isPullback_morphismRestrict g' U).paste_vert hpb).w
      ((derivedPullback U.ι.toLRSHom.toShHom).obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op E)).obj K))
      ((derivedPullback (g' ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj
        (((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
          (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).obj K'))
      (pullDatum (g' ∣_ U).toLRSHom.toShHom (g' ⁻¹ᵁ U).ι.toLRSHom.toShHom
        U.ι.toLRSHom.toShHom g'.toLRSHom.toShHom (comp_toShHom_of_comm (morphismRestrict_ι g' U))
        _ _ (baseChangeSheafHomComparison g'.toLRSHom.toShHom E K K' φ)) y n) ↔
    IsIso (baseChangeCohomologyMap (U.ι ≫ f) g ((g' ⁻¹ᵁ U).ι ≫ f') (g' ∣_ U)
      ((isPullback_morphismRestrict g' U).paste_vert hpb).w
      (((Stacks.SheafOfModules.derivedSheafHom U.toScheme.sheaf).obj
        (op ((derivedPullback U.ι.toLRSHom.toShHom).obj E))).obj
          ((derivedPullback U.ι.toLRSHom.toShHom).obj K))
      (((Stacks.SheafOfModules.derivedSheafHom (g' ⁻¹ᵁ U).toScheme.sheaf).obj
        (op ((derivedPullback (g' ∣_ U).toLRSHom.toShHom).obj
          ((derivedPullback U.ι.toLRSHom.toShHom).obj E)))).obj
            ((derivedPullback (g' ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj K'))
      (baseChangeSheafHomComparison (g' ∣_ U).toLRSHom.toShHom
        ((derivedPullback U.ι.toLRSHom.toShHom).obj E)
        ((derivedPullback U.ι.toLRSHom.toShHom).obj K)
        ((derivedPullback (g' ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj K')
        (pullDatum (g' ∣_ U).toLRSHom.toShHom (g' ⁻¹ᵁ U).ι.toLRSHom.toShHom
          U.ι.toLRSHom.toShHom g'.toLRSHom.toShHom
          (comp_toShHom_of_comm (morphismRestrict_ι g' U)) K K' φ)) y n) := by
  have hθ := isIso_derivedPullbackSheafHomMap_opensι U E K
  have hν' := isIso_derivedPullbackSheafHomMap_opensι (g' ⁻¹ᵁ U)
    ((derivedPullback g'.toLRSHom.toShHom).obj E) K'
  have key := map_derivedPullbackSheafHomMap_comp_baseChangeSheafHomComparison_pullDatum
    (g' ∣_ U).toLRSHom.toShHom (g' ⁻¹ᵁ U).ι.toLRSHom.toShHom U.ι.toLRSHom.toShHom
    g'.toLRSHom.toShHom (comp_toShHom_of_comm (morphismRestrict_ι g' U)) E K K' φ
  have hH := Iso.isIso_hom
    (((Stacks.SheafOfModules.derivedSheafHom (g' ⁻¹ᵁ U).toScheme.sheaf).mapIso
      ((derivedPullbackCompIsoCanonical (g' ∣_ U).toLRSHom.toShHom U.ι.toLRSHom.toShHom).app E ≪≫
        ((derivedPullbackCompIsoLeft (g' ∣_ U).toLRSHom.toShHom (g' ⁻¹ᵁ U).ι.toLRSHom.toShHom
          U.ι.toLRSHom.toShHom g'.toLRSHom.toShHom
          (comp_toShHom_of_comm (morphismRestrict_ι g' U))).app E).symm).op).app
      ((derivedPullback (g' ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj K'))
  have hψ := IsIso.comp_isIso' hν' hH
  have ht := isIso_baseChangeCohomologyMap_iff_of_isIso_target (U.ι ≫ f) g
    ((g' ⁻¹ᵁ U).ι ≫ f') (g' ∣_ U) ((isPullback_morphismRestrict g' U).paste_vert hpb).w
    ((derivedPullback U.ι.toLRSHom.toShHom).obj
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op E)).obj K)) _ _
    (pullDatum (g' ∣_ U).toLRSHom.toShHom (g' ⁻¹ᵁ U).ι.toLRSHom.toShHom
        U.ι.toLRSHom.toShHom g'.toLRSHom.toShHom (comp_toShHom_of_comm (morphismRestrict_ι g' U))
        _ _ (baseChangeSheafHomComparison g'.toLRSHom.toShHom E K K' φ)) _ hψ y n
  exact ht.symm.trans (isIso_baseChangeCohomologyMap_iff_of_eq_map_comp (U.ι ≫ f) g
    ((g' ⁻¹ᵁ U).ι ≫ f') (g' ∣_ U) ((isPullback_morphismRestrict g' U).paste_vert hpb).w _ _ _ _
    hθ _ _ key.symm y n)

end AlgebraicGeometry

end
