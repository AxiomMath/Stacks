module

public import Mathlib.GroupTheory.OrderOfElement
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SurjectiveMorphismStalkDescent
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs

/-!
# A constructible abelian étale sheaf is torsion

A constructible sheaf of abelian groups on the small étale site of a scheme is a torsion abelian
sheaf, and torsion descends along a surjective morphism whose inverse image is constructible:
if `f : X ⟶ Y` is surjective and `f⁻¹ℱ` is constructible, then `ℱ` is torsion. No hypothesis on
the schemes is needed for either statement.

Torsion of an abelian sheaf on a site is the *local* condition
`Stacks.Torsion.torsionSheafProperty` of Stacks 0DD7: every section is annihilated, after
restriction along the arrows of a covering sieve, by a positive integer which may vary over the
sieve.

## Main results

* `Stacks.Torsion.torsionSheafProperty_of_forall_overPullback` — torsion of an abelian sheaf is
  local on the site.
* `Stacks.Torsion.torsionSheafProperty_of_isFiniteLocallyConstant` — a finite locally constant
  abelian sheaf on any site is torsion.
* `AlgebraicGeometry.exists_nsmul_eq_zero_etaleStalk_of_isConstructibleAbelianSheaf` — the
  geometric stalks of a constructible abelian étale sheaf are torsion groups.
* `AlgebraicGeometry.torsionSheafProperty_of_isConstructibleAbelianSheaf` — a constructible
  abelian étale sheaf is torsion.
* `AlgebraicGeometry.torsionSheafProperty_of_isConstructibleAbelianSheaf_pullback` — an abelian
  étale sheaf whose inverse image along a surjective morphism is constructible is torsion.

## Implementation notes

The coefficient universe is `AddCommGrpCat.{u + 1}`, as in the rest of the constructibility
development, `u` being the universe of the schemes.

`AlgebraicGeometry.IsTorsionAbelianSheaf` is the *pointwise* condition that every section over
every étale object is annihilated by a positive integer. It implies
`Stacks.Torsion.torsionSheafProperty`
(`AlgebraicGeometry.torsionSheafProperty_of_isTorsionAbelianSheaf`), and the converse is not
available: the objects of the small étale site need not be quasi-compact, so a section over such
an object may meet infinitely many strata and the positive integers annihilating it on the
members of a covering admit no common multiple.

The geometric half goes through the stalk criterion for torsion of Stacks 0GJX
(`StacksFrontier/AlgebraicGeometry/Etale/FShriekTorsion.lean`), since the strata of a constructible
stratification are locally closed subschemes and not étale coverings.

## References

* [Stacks Project, Tag 095Q](https://stacks.math.columbia.edu/tag/095Q)
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
* [Stacks Project, Tag 0GJX](https://stacks.math.columbia.edu/tag/0GJX)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Torsion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The torsion sieve of a restriction of a section is the pullback of its torsion sieve. -/
public theorem torsionSieve_map (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) {U V : C} (g : V ⟶ U)
    (y : P.obj (op U)) :
    torsionSieve P (P.map g.op y) = (torsionSieve P y).pullback g := by
  have hres : ∀ {W : C} (h : W ⟶ V),
      P.map (h ≫ g).op y = P.map h.op (P.map g.op y) := by
    intro W h
    rw [op_comp, P.map_comp, CategoryTheory.comp_apply]
  ext W h
  show (∃ n : ℕ, 0 < n ∧ n • P.map h.op (P.map g.op y) = 0) ↔
    ∃ n : ℕ, 0 < n ∧ n • P.map (h ≫ g).op y = 0
  rw [hres h]

/-- **Torsion of an abelian sheaf is local on the site.** If every object of the site has a
covering family on each member of which the restricted sheaf is torsion, the sheaf is torsion. -/
public theorem torsionSheafProperty_of_forall_overPullback (F : Sheaf J AddCommGrpCat.{w})
    (h : ∀ U : C, ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧ ∀ i,
        torsionSheafProperty (J.over (X i))
          ((J.overPullback AddCommGrpCat.{w} (X i)).obj F)) :
    torsionSheafProperty J F := by
  rw [torsionSheafProperty_iff_isLocallyTorsion, isLocallyTorsion_iff_torsionSieve_mem]
  intro U x
  obtain ⟨I, X, f, hcov, hloc⟩ := h U
  refine J.transitive hcov _ fun W g hg => ?_
  obtain ⟨-, k, -, ⟨i⟩, rfl⟩ := hg
  rw [← torsionSieve_map]
  obtain ⟨R, hR, hkill⟩ := hloc i (Over.mk k) (F.obj.map (k ≫ f i).op x)
  rw [GrothendieckTopology.mem_over_iff] at hR
  exact J.superset_covering
    ((Sieve.overEquiv (Over.mk k)).le_symm_apply.mp fun Z c hc => hkill Z c hc) hR

/-- **A constant abelian sheaf with finite value is torsion.** -/
public theorem torsionSheafProperty_constantSheaf [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] (E : AddCommGrpCat.{w}) [Finite E] :
    torsionSheafProperty J ((constantSheaf J AddCommGrpCat.{w}).obj E) := by
  refine torsionSheafProperty_sheafify J ((Functor.const Cᵒᵖ).obj E) fun U y => ?_
  refine ⟨⊤, J.top_mem U, fun V g _ => ⟨Nat.card E, Nat.card_pos, ?_⟩⟩
  show Nat.card E • y = 0
  exact card_nsmul_eq_zero'

/-- **A finite locally constant abelian sheaf is torsion.** -/
public theorem torsionSheafProperty_of_isFiniteLocallyConstant
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F : Sheaf J AddCommGrpCat.{w})
    (hF : Stacks.ConstantSheaf.IsFiniteLocallyConstant J F) :
    torsionSheafProperty J F := by
  refine torsionSheafProperty_of_forall_overPullback J F fun U => ?_
  obtain ⟨I, X, f, hcov, htriv⟩ := hF.exists_finite_cover U
  refine ⟨I, X, f, hcov, fun i => ?_⟩
  obtain ⟨E, hEfin, ⟨e⟩⟩ := htriv i
  have : Finite E := hEfin
  exact torsionSheafProperty_of_iso _ e (torsionSheafProperty_constantSheaf _ E)

end Stacks.Torsion

namespace AlgebraicGeometry

open Stacks.Torsion

variable (B : BigEtaleSite.{u})

/-- Sheafification equivalences are the local bijections on a localized small étale site, at the
coefficient universe of the site. -/
private instance wEqualsLocallyBijective_smallEtale_over (T : B.Scheme)
    (V : SmallEtale B T.obj T.property) :
    ((SmallEtale.topology B T.obj T.property).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall.{u + 1, u + 1, u} _

/-- A pointwise torsion abelian étale sheaf is torsion. -/
public theorem torsionSheafProperty_of_isTorsionAbelianSheaf (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsTorsionAbelianSheaf B X F) :
    torsionSheafProperty (SmallEtale.topology B X.obj X.property) F := fun U x =>
  ⟨⊤, (SmallEtale.topology B X.obj X.property).top_mem U,
    fun V g _ => hF V (F.obj.map g.op x)⟩

/-- If the stalks of the inverse image of `F` along `f` at `x` are torsion, so is the stalk of `F`
at any geometric point with the same image as `x`. -/
private theorem exists_nsmul_eq_zero_etaleStalk_of_pullback {X Y : B.Scheme} (f : X ⟶ Y)
    [((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).IsRightAdjoint]
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
    (x : GeometricPoint X.obj) (s : GeometricPoint Y.obj)
    (hx : (x.map (B.inclusion.map f)).hom default = s.hom default)
    (h : ∀ z : ↑(etaleStalk B X.obj X.property x
      (((smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).obj F).obj), ∃ n : ℕ, 0 < n ∧ n • z = 0)
    (g : ↑(etaleStalk B Y.obj Y.property s F.obj)) :
    ∃ n : ℕ, 0 < n ∧ n • g = 0 := by
  refine exists_nsmul_eq_zero_of_iso
    ((etaleStalkPresheafFunctorIsoOfEqBase B Y.obj Y.property hx
      AddCommGrpCat.{u + 1}).app F.obj) (fun y => ?_) g
  exact exists_nsmul_eq_zero_of_iso
    (etaleStalkSmallEtalePullObjIso B f x AddCommGrpCat.{u + 1} F) h y

section Stalks

variable
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- **The geometric stalks of a constructible abelian étale sheaf are torsion groups.** -/
public theorem exists_nsmul_eq_zero_etaleStalk_of_isConstructibleAbelianSheaf (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) (t : GeometricPoint X.obj)
    (g : ↑(etaleStalk B X.obj X.property t F.obj)) :
    ∃ n : ℕ, 0 < n ∧ n • g = 0 := by
  obtain ⟨U, hU⟩ : ∃ U : X.obj.affineOpens, t.hom default ∈ (U.1 : Set X.obj) := by
    have h : t.hom default ∈ (⊤ : X.obj.Opens) := trivial
    rw [← iSup_affineOpens_eq_top X.obj] at h
    exact TopologicalSpace.Opens.mem_iSup.mp h
  obtain ⟨s, hs⟩ := hF U
  obtain ⟨i, z, hz⟩ : ∃ (i : Fin s.n) (z : (s.piece i).obj),
      (B.inclusion.map (s.inclusion i)).base z = t.hom default := by
    have hx : t.hom default ∈ ⋃ i, Set.range (B.inclusion.map (s.inclusion i)).base := by
      rw [← s.covers]; exact hU
    exact Set.mem_iUnion.mp hx
  set t' := GeometricPoint.ofPoint (s.piece i).obj z with ht'
  have hbase : (t'.map (B.inclusion.map (s.inclusion i))).hom default = t.hom default := by
    show (B.inclusion.map (s.inclusion i)).base (t'.hom default) = t.hom default
    rwa [show t'.hom default = z from GeometricPoint.ofPoint_liesOver (s.piece i).obj z]
  have hG : torsionSheafProperty
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
      (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F) :=
    torsionSheafProperty_of_isFiniteLocallyConstant _ _ (hs i)
  exact exists_nsmul_eq_zero_etaleStalk_of_pullback B (s.inclusion i) F t' _ hbase
    (SmallEtale.exists_nsmul_eq_zero_etaleStalk.{u, u + 1} B (s.piece i).obj
      (s.piece i).property t' _ hG) g

/-- **A constructible abelian étale sheaf is torsion.** -/
public theorem torsionSheafProperty_of_isConstructibleAbelianSheaf (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) :
    torsionSheafProperty (SmallEtale.topology B X.obj X.property) F :=
  SmallEtale.torsionSheafProperty_of_forall_etaleStalk.{u, u + 1} B X.obj X.property F
    fun t g => exists_nsmul_eq_zero_etaleStalk_of_isConstructibleAbelianSheaf B X F hF t g

/-- **Torsion of an abelian étale sheaf descends along a surjective morphism whose inverse image
is constructible.** Let `f : X ⟶ Y` be surjective and `ℱ` an abelian sheaf on `Y_étale` whose
inverse image is constructible. Then `ℱ` is torsion. -/
public theorem torsionSheafProperty_of_isConstructibleAbelianSheaf_pullback
    {X Y : B.Scheme} (f : X ⟶ Y) (hf : Function.Surjective (B.inclusion.map f).base)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X ((smallEtaleAbelianPullbackFunctor B f).obj F)) :
    torsionSheafProperty (SmallEtale.topology B Y.obj Y.property) F := by
  refine SmallEtale.torsionSheafProperty_of_forall_etaleStalk.{u, u + 1} B Y.obj Y.property F
    fun s g => ?_
  obtain ⟨x, hx⟩ := exists_geometricPoint_map_hom_base_eq_of_surjective (B.inclusion.map f) hf s
  exact exists_nsmul_eq_zero_etaleStalk_of_pullback B f F x s hx
    (exists_nsmul_eq_zero_etaleStalk_of_isConstructibleAbelianSheaf B X _ hF x) g

end Stalks

end AlgebraicGeometry

end
