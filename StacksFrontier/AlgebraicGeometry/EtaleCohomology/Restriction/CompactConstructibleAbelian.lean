module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Presentable.Finite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.ShriekConstantPresentable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.SmallEtaleFiniteCoverings

/-!
# The abelian case of compactness of constructible étale sheaves

Stacks 09Z4 asserts that morphisms out of a constructible sheaf on the small étale site of a
quasi-compact quasi-separated scheme commute with filtered colimits, for sheaves of sets, of
abelian groups, and of modules over a Noetherian ring. The three cases are not independent: an
abelian group is a `ℤ`-module, and `ℤ` is Noetherian, so the abelian case is the module case at
`R = ℤ`.

This file makes that reduction precise and proves it. Under the equivalence
`AddCommGrpCat ≌ ModuleCat ℤ` and the induced equivalence of sheaf categories, a constructible
abelian sheaf becomes a constructible sheaf of `ℤ`-modules
(`AlgebraicGeometry.isConstructibleModuleSheaf_moduleCatIntEquivalence`), and finite
presentability transports back across an equivalence of categories. So the abelian case of
Stacks 09Z4 follows from its module case with no further geometric input; nothing here depends on
the module case being known.

The translation of constructibility is the only part with content. Constructibility is local
constancy with finite values after restriction to the strata of a constructible stratification,
so it has to be moved past both the restriction along a stratum and the restriction to a slice
site; that is what `CategoryTheory.Sheaf.sheafPullbackCoefficientIso` and
`CategoryTheory.Sheaf.constantSheafCoefficientIso` are for, and a finite abelian group becomes a
finitely generated `ℤ`-module.

## Main results

* `AlgebraicGeometry.isFiniteTypeLocallyConstant_moduleCatIntEquivalence` — a finite locally
  constant abelian sheaf becomes a locally constant sheaf of finitely generated `ℤ`-modules.
* `AlgebraicGeometry.isConstructibleModuleSheaf_moduleCatIntEquivalence` — a constructible
  abelian étale sheaf becomes a constructible sheaf of `ℤ`-modules.
* `CategoryTheory.preservesFilteredColimitsOfSize_preadditiveCoyoneda` — for a finitely
  presentable object of a preadditive category, the abelian-group-valued Hom functor preserves
  filtered colimits.
* `AlgebraicGeometry.preservesFilteredColimits_preadditiveCoyoneda_of_isFinitelyPresentable_int`
  — the two combined: the abelian form of Stacks 09Z4 for `F`, given its module form for the
  `ℤ`-module sheaf attached to `F`.

## Implementation notes

A cocone of abelian groups over a filtered diagram is a colimit as soon as its underlying cocone
of sets is one: the induced map is additive because any two elements of a filtered colimit come
from a common stage. `CategoryTheory.isColimit_of_forget_addCommGrpCat` records this, and it is
what turns preservation of filtered colimits by the set-valued Hom functor — which is the
definition of finite presentability — into preservation by the abelian-group-valued one.

## References

* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u a

namespace CategoryTheory

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- A cocone of abelian groups over a filtered diagram whose underlying cocone of sets is a
colimit is itself a colimit. The induced map is additive because any two elements of a filtered
colimit of sets lift to a common stage of the diagram. -/
public def isColimit_of_forget_addCommGrpCat
    {I : Type w} [Category.{v} I] [IsFilteredOrEmpty I]
    {F : I ⥤ AddCommGrpCat.{u}} (c : Cocone F)
    (hc : IsColimit ((forget AddCommGrpCat).mapCocone c)) : IsColimit c := by
  have hfac (s : Cocone F) (j : I) (x : F.obj j) :
      hc.desc ((forget AddCommGrpCat).mapCocone s) ((c.ι.app j) x) = (s.ι.app j) x :=
    ConcreteCategory.congr_hom (hc.fac ((forget AddCommGrpCat).mapCocone s) j) x
  refine
    { desc := fun s => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (hc.desc ((forget AddCommGrpCat).mapCocone s)) ?_)
      fac := ?_
      uniq := ?_ }
  · intro x y
    obtain ⟨j, x', y', hx, hy⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ hc x y
    change (c.ι.app j) x' = x at hx
    change (c.ι.app j) y' = y at hy
    subst x; subst y
    rw [← map_add, hfac, hfac, hfac, map_add]
  · intro s j
    ext x
    exact hfac s j x
  · intro s m hm
    apply (forget AddCommGrpCat).map_injective
    exact hc.uniq ((forget AddCommGrpCat).mapCocone s) ((forget AddCommGrpCat).map m)
      (fun j => by
        change (forget AddCommGrpCat).map (c.ι.app j) ≫ (forget AddCommGrpCat).map m = _
        rw [← Functor.map_comp, hm j]
        rfl)

/-- For a finitely presentable object of a preadditive category, the abelian-group-valued Hom
functor preserves filtered colimits. Finite presentability is the same statement for the
set-valued Hom functor, and a cocone of abelian groups over a filtered diagram is a colimit as
soon as its underlying cocone of sets is. -/
public theorem preservesFilteredColimitsOfSize_preadditiveCoyoneda
    {D : Type u} [Category.{v} D] [Preadditive D] (F : D) [IsFinitelyPresentable.{w} F] :
    PreservesFilteredColimitsOfSize.{w, w} (preadditiveCoyoneda.obj (op F)) := by
  refine ⟨fun {I} _ _ => ⟨fun {G} => ⟨fun {c} hc => ?_⟩⟩⟩
  exact ⟨isColimit_of_forget_addCommGrpCat _ (isColimitOfPreserves (coyoneda.obj (op F)) hc)⟩

end CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- A finite locally constant sheaf of abelian groups becomes, under the equivalence with
`ℤ`-modules, a locally constant sheaf of finitely generated `ℤ`-modules: the same trivializing
cover works, and a finite abelian group is a finitely generated `ℤ`-module. -/
public theorem isFiniteTypeLocallyConstant_moduleCatIntEquivalence
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v a}]
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{max u v a} ℤ)]
    (F : Sheaf J AddCommGrpCat.{max u v a})
    (hF : Stacks.ConstantSheaf.IsFiniteLocallyConstant J F)
    (Q : Sheaf J (ModuleCat.{max u v a} ℤ))
    (eQ : (sheafCompose J AddCommGrpCat.moduleCatIntEquivalence.{max u v a}.functor).obj F ≅ Q) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant ℤ J Q := by
  intro U
  obtain ⟨I, V, f, hf, hV⟩ := hF.exists_finite_cover U
  refine ⟨I, V, f, hf, fun i => ?_⟩
  obtain ⟨A, hA, ⟨eA⟩⟩ := hV i
  have := hA
  refine ⟨AddCommGrpCat.moduleCatIntEquivalence.functor.obj A,
    (ModuleCat.isFG_iff _).2 (AddCommGrpCat.moduleFinite_moduleCatIntEquivalence_obj A), ⟨?_⟩⟩
  exact ((Sheaf.constantSheafCoefficientIso (J.over (V i))
      AddCommGrpCat.moduleCatIntEquivalence.{max u v a}).app A).symm ≪≫
    (sheafCompose (J.over (V i))
      AddCommGrpCat.moduleCatIntEquivalence.{max u v a}.functor).mapIso eA ≪≫
    (J.overPullback (ModuleCat.{max u v a} ℤ) (V i)).mapIso eQ

/-- A constructible sheaf of abelian groups on the small étale site becomes a constructible
sheaf of `ℤ`-modules. Constructibility is finite local constancy on the strata of a
constructible stratification of every affine open, so the same stratification works and only the
coefficient translation has to be pushed past restriction to a stratum. -/
public theorem isConstructibleModuleSheaf_moduleCatIntEquivalence
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) AddCommGrpCat.{u + 1}]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} ℤ)
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{u + 1} ℤ)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) :
    IsConstructibleModuleSheaf B X ℤ
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property)
        AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor.obj F) := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i => ?_⟩
  exact isFiniteTypeLocallyConstant_moduleCatIntEquivalence.{u, u + 1, 0} _ _ (hs i) _
    ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B (s.inclusion i))
      (SmallEtale.topology B X.1 X.property)
      (SmallEtale.topology B (s.piece i).1 (s.piece i).property)
      AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).app F)

/-- A sheaf of abelian groups is finitely presentable once the attached `ℤ`-module sheaf is. -/
private theorem isFinitelyPresentable_of_coefficientEquivalence_int (B : BigEtaleSite.{u})
    (X : B.Scheme)
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) AddCommGrpCat.{u + 1}]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{u + 1} ℤ)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (hFP : IsFinitelyPresentable.{w}
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property)
        AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor.obj F)) :
    IsFinitelyPresentable.{w} F :=
  (isCardinalPresentable_iff_of_isEquivalence F Cardinal.aleph0.{w}
    (Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property)
      AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor).1 hFP

/-- **The abelian case of Stacks 09Z4, reduced to its module case.** If the sheaf of
`ℤ`-modules attached to `F` is finitely presentable, then the abelian-group-valued Hom functor
out of `F` preserves filtered colimits.

Composed with the module case of Stacks 09Z4 at `R = ℤ` applied to
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleCatIntEquivalence`, this is the abelian case
for every constructible abelian sheaf on a quasi-compact quasi-separated scheme. -/
public theorem preservesFilteredColimits_preadditiveCoyoneda_of_isFinitelyPresentable_int
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) AddCommGrpCat.{u + 1}]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{u + 1} ℤ)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (hFP : IsFinitelyPresentable.{w}
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property)
        AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor.obj F)) :
    PreservesFilteredColimitsOfSize.{w, w} (preadditiveCoyoneda.obj (op F)) := by
  have := isFinitelyPresentable_of_coefficientEquivalence_int B X F hFP
  exact preservesFilteredColimitsOfSize_preadditiveCoyoneda F

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

/-- **The extension by zero of the constant free rank-one `ℤ`-module sheaf is finitely
presentable**, for an étale object `U` of `X` all of whose coverings are refined by finite
coverings with quasi-compact fibre products.

This is `AlgebraicGeometry.isFinitelyPresentable_moduleShriekConstant` with the ring in `Type 0`
instead of `Type (u + 1)`. The module universe is `u + 1` either way, because the ring universe
enters it only through a `max`, so the same argument applies verbatim; the statement has to be
repeated only because `ℤ` is not a ring in `Type (u + 1)`. -/
public theorem isFinitelyPresentable_moduleShriekConstant_int (B : BigEtaleSite.{u})
    (X : B.Scheme) (U : SmallEtale B X.1 X.property)
    (H : (SmallEtale.topology B X.1 X.property).HasFiniteQuasiCompactCoverings U) :
    IsFinitelyPresentable.{u + 1} (moduleShriekConstant.{u, 0, u + 1} B X ℤ U) := by
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, u + 1} B X ℤ
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, u + 1} B U.obj.left ℤ
  let := ModuleCat.isFinitelyPresentable_uliftSelf.{0, u + 1} ℤ
  refine Sheaf.isFinitelyPresentable_sheafPullback_constantSheaf
    (smallEtalePostcompose B X.1 X.property U) _ _ _
    (SmallEtale.finalIsTerminal B U.obj.left.1 U.obj.left.property) _ ?_
  have h := Sheaf.preservesFilteredColimitsOfSize_sheafSections_moduleCat.{0, u, u + 1}
    (SmallEtale.topology B X.1 X.property) ℤ H
  refine ⟨fun {I} _ _ => ?_⟩
  exact preservesColimitsOfShape_of_natIso
    ((sheafSections (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} ℤ)).mapIso
      (smallEtalePostcomposeFinalIso B X U).op)

/-- **A finite shriek presentation makes a sheaf of `ℤ`-modules finitely presentable.** This is
`AlgebraicGeometry.isFinitelyPresentable_of_hasFiniteShriekPresentation` at the ring `ℤ`, which
lives in `Type 0` rather than in `Type (u + 1)`. -/
public theorem isFinitelyPresentable_of_hasFiniteShriekPresentation_int (B : BigEtaleSite.{u})
    (X : B.Scheme) (P : SmallEtale B X.1 X.property → Prop)
    (hP : ∀ W, P W → (SmallEtale.topology B X.1 X.property).HasFiniteQuasiCompactCoverings W)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} ℤ))
    (h : HasFiniteShriekPresentation.{u, 0, u + 1} B X ℤ P F) :
    IsFinitelyPresentable.{u + 1} F := by
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, u + 1} B X ℤ
  obtain ⟨n, m, U, V, hU, hV, f, ⟨e⟩⟩ := h
  have hsig : ∀ {k : ℕ} (W : Fin k → SmallEtale B X.1 X.property), (∀ i, P (W i)) →
      IsFinitelyPresentable.{u + 1}
        (∐ fun i => moduleShriekConstant.{u, 0, u + 1} B X ℤ (W i)) := by
    intro k W hW
    have : ∀ j : Discrete (Fin k), IsFinitelyPresentable.{u + 1}
        ((Discrete.functor fun i =>
          moduleShriekConstant.{u, 0, u + 1} B X ℤ (W i)).obj j) := by
      rintro ⟨i⟩
      exact isFinitelyPresentable_moduleShriekConstant_int B X (W i) (hP _ (hW i))
    exact isFinitelyPresentable_of_isColimit_of_finCategory _ (colimit.isColimit _)
  have h0 := hsig V hV
  have h1 := hsig U hU
  have hcoker : IsFinitelyPresentable.{u + 1} (cokernel f) := by
    have : ∀ j : WalkingParallelPair,
        IsFinitelyPresentable.{u + 1} ((parallelPair f 0).obj j) := by
      rintro (_ | _)
      · exact h0
      · exact h1
    exact isFinitelyPresentable_of_isColimit_of_finCategory _
      (colimit.isColimit (parallelPair f 0))
  let eF : cokernel f ≅ F :=
    (sheafToPresheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} ℤ)).preimageIso
      (e ≪≫ Functor.isoWhiskerLeft F.obj (ModuleCat.uliftFunctorSelfIso.{0, u + 1} ℤ) ≪≫
        F.obj.rightUnitor)
  exact isCardinalPresentable_of_iso eF _

/-- **The sheaves-of-abelian-groups case of Stacks 09Z4.** Let `X` be a quasi-compact
quasi-separated scheme and let `F` be a constructible abelian sheaf on `X_étale`. Then morphisms
out of `F` commute with filtered colimits of abelian sheaves:
`Mor(F, colim G_i) = colim Mor(F, G_i)`.

A constructible abelian sheaf is a constructible sheaf of `ℤ`-modules and `ℤ` is Noetherian, so
this is the module case at `Λ = ℤ`. Stacks 095N for `ℤ`-modules — the presentation as the cokernel
of a map between finite direct sums of extensions by zero of constant free rank-one module sheaves
at quasi-compact quasi-separated étale objects — is carried as the hypothesis `h095N`. It is a
special case of `AlgebraicGeometry.IsConstructibleAbelianSheaf.isFinitelyPresentable`, which proves
Stacks 095N for `ℤ`-modules. -/
public theorem isFinitelyPresentable_of_isConstructibleAbelianSheaf (B : BigEtaleSite.{u})
    (X : B.Scheme) [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) AddCommGrpCat.{u + 1}]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} ℤ)
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{u + 1} ℤ)]
    (h095N : ∀ G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} ℤ),
      IsConstructibleModuleSheaf B X ℤ G →
        HasFiniteShriekPresentation.{u, 0, u + 1} B X ℤ
          (fun W ↦ CompactSpace ((SmallEtale.toScheme B X.1 X.property).obj W) ∧
            QuasiSeparatedSpace ((SmallEtale.toScheme B X.1 X.property).obj W)) G)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) :
    IsFinitelyPresentable.{u + 1} F := by
  have hFP : IsFinitelyPresentable.{u + 1}
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property)
        AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor.obj F) :=
    isFinitelyPresentable_of_hasFiniteShriekPresentation_int B X _
      (fun W hW ↦ SmallEtale.hasFiniteQuasiCompactCoverings B X W hW.1 hW.2) _
      (h095N _ (isConstructibleModuleSheaf_moduleCatIntEquivalence B X F hF))
  exact isFinitelyPresentable_of_coefficientEquivalence_int B X F hFP

end AlgebraicGeometry

end
