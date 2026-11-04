module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.CategoryTheory.Functor.ConjugateQuotient
import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# Functoriality of the functor of quotients in the test scheme

`AlgebraicGeometry.Space.QuotientSituation.quotients` is the set `Q_{F/X/Y}(T)` of Stacks 082M,
for one test scheme `T` over `Y` at a time. For a morphism `h : T' ⟶ T` of test schemes, a
quotient `F_T ⟶ Q` pulls back to `F_{T'} ⟶ (X_{T'} ⟶ X_T)^*Q`, and the resulting assignment is
the functor

`Q_{F/X/Y} : (Sch/Y)ᵒᵖ ⥤ Sets`

of Stacks 082N, with the subfunctor `Q^{fp}_{F/X/Y}` of Stacks 0CZL cut out by finite
presentation.

## Main definitions

* `AlgebraicGeometry.Space.QuotientSituation.toHomSituation`: the relative Hom situation of
  Stacks 08JT on the same morphism.
* `AlgebraicGeometry.Space.QuotientSituation.baseChangeComparison`: the comparison
  `F_{T'} ≅ (X_{T'} ⟶ X_T)^*F_T`, at the level of the inverse-image functors.
* `AlgebraicGeometry.Space.QuotientSituation.quotientPullbackProjection`: the projection
  `F_{T'} ⟶ (X_{T'} ⟶ X_T)^*(F_T/K)` presenting the pulled-back quotient.
* `AlgebraicGeometry.Space.QuotientSituation.quotientPullback`: the pullback of a quotient of
  `F_T` along a morphism of test schemes, recorded by its kernel.
* `AlgebraicGeometry.Space.QuotientSituation.quotientPullbackCokernelIso`: the pulled-back
  quotient is the inverse image of the quotient.
* `AlgebraicGeometry.Space.QuotientSituation.PullbackPreservesFlatOver`: the inverse image along
  the base-change maps of the situation preserves quasi-coherent modules flat over the base.
* `AlgebraicGeometry.Space.QuotientSituation.PullbackPreservesFinitePresentation`: the inverse
  image along the base-change maps of the situation preserves finite presentation.
* `AlgebraicGeometry.Space.QuotientSituation.quotientsFunctor`: the functor of quotients of
  `F/X/Y`.
* `AlgebraicGeometry.Space.QuotientSituation.finitePresentationQuotientsFunctor`: its
  finite-presentation subfunctor.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.quotientPullback_id` and
  `AlgebraicGeometry.Space.QuotientSituation.quotientPullback_comp`: pullback of quotients is
  functorial in the test scheme.
* `AlgebraicGeometry.Space.QuotientSituation.pullbackPreservesFlatOver` and
  `AlgebraicGeometry.Space.QuotientSituation.pullbackPreservesFinitePresentation`: the two
  preservation properties hold.
* `AlgebraicGeometry.Space.QuotientSituation.quotientPullback_mem_quotients'` and
  `AlgebraicGeometry.Space.QuotientSituation.quotientPullback_mem_finitePresentationQuotients`:
  the pullback of a quotient in `Q_{F/X/Y}(T)` lies in `Q_{F/X/Y}(T')`, and likewise for
  finitely presented quotients.
* `AlgebraicGeometry.Space.QuotientSituation.isQuasicoherentOnSite_quotientPullback`,
  `AlgebraicGeometry.Space.QuotientSituation.isFlatOver_quotientPullback` and
  `AlgebraicGeometry.Space.QuotientSituation.isFinitePresentationOnSite_quotientPullback`: the
  same three conditions for the pullback of a quotient of finite presentation.
* `AlgebraicGeometry.Space.QuotientSituation.baseChangeComparison_id` and
  `AlgebraicGeometry.Space.QuotientSituation.baseChangeComparison_comp`: the two coherences of
  the base-change comparison.

## References

* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The inverse image of `𝒪`-modules along any morphism of algebraic spaces preserves
epimorphisms. -/
instance modulePullback_preservesEpimorphisms {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (modulePullback B S hS f).PreservesEpimorphisms :=
  Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS f)

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-! ### The base-change comparison -/

/-- The relative Hom situation of Stacks 08JT on the morphism of the quotient situation, with
its module in both slots. -/
def toHomSituation : HomSituation B S hS where
  X := D.X
  base := D.Y
  f := D.f
  F := D.F
  G := D.F
  quasicoherent_F := D.quasicoherent
  quasicoherent_G := D.quasicoherent

/-- The comparison of the base change of `F` to `T'` with the base change to `T` followed by
the inverse image along `X_{T'} ⟶ X_T`, as an isomorphism of the two inverse-image functors.
At `F` it is the identification `F_{T'} ≅ (X_{T'} ⟶ X_T)^*F_T`. -/
def baseChangeComparison {T' T : SchemesOver D.Y} (h : T' ⟶ T) :
    modulePullback B S hS (D.sourceProjection T') ≅
      modulePullback B S hS (D.sourceProjection T) ⋙
        modulePullback B S hS (D.relativeMap h) :=
  modulePullbackTriangle B S hS (baseChangeMap_comp_projection D.f h)

/-- The comparison for the identity morphism of a test scheme is whiskering by the unit law
`(𝟙 X_T)^* ≅ 𝟭` of Stacks 03LU, corrected by the identification of `X_T ⟶ X_T` with the
identity. -/
theorem baseChangeComparison_id (hc : ModulePushforwardCoherence B S hS)
    (T : SchemesOver D.Y) :
    D.baseChangeComparison (𝟙 T) =
      (Functor.rightUnitor (modulePullback B S hS (D.sourceProjection T))).symm ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS (D.sourceProjection T))
          ((hc.modulePullbackIdIso (D.space T)).symm ≪≫
            eqToIso (congrArg (modulePullback B S hS) (baseChangeMap_id D.f T).symm)) :=
  D.toHomSituation.baseChangeComparison_id hc T

/-- The comparison for a composite of morphisms of test schemes, in terms of the comparisons
for the two factors and the comparison of Stacks 03LU for the two base-change maps. -/
theorem baseChangeComparison_comp (hc : ModulePushforwardCoherence B S hS)
    {T'' T' T : SchemesOver D.Y} (h : T'' ⟶ T') (k : T' ⟶ T) :
    D.baseChangeComparison (h ≫ k) =
      (D.baseChangeComparison h ≪≫
          Functor.isoWhiskerRight (D.baseChangeComparison k)
            (modulePullback B S hS (D.relativeMap h)) ≪≫
          Functor.associator (modulePullback B S hS (D.sourceProjection T))
            (modulePullback B S hS (D.relativeMap k))
            (modulePullback B S hS (D.relativeMap h))) ≪≫
        (Functor.isoWhiskerLeft (modulePullback B S hS (D.sourceProjection T))
          (modulePullbackTriangle B S hS (baseChangeMap_comp D.f h k).symm)).symm :=
  D.toHomSituation.baseChangeComparison_comp hc h k

/-! ### Pullback of a quotient -/

/-- The projection of `F_{T'}` onto the inverse image of the quotient `F_T/K` along
`X_{T'} ⟶ X_T`: the inverse image of the projection `F_T ⟶ F_T/K`, read through the comparison
of the two base changes. -/
def quotientPullbackProjection {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) :
    D.baseChangeModule T' ⟶
      (modulePullback B S hS (D.relativeMap h)).obj (D.quotientModule T K) :=
  Functor.conjQuotientProjection (D.baseChangeComparison h) K

/-- The projection onto the pulled-back quotient is an epimorphism. -/
instance epi_quotientPullbackProjection {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) : Epi (D.quotientPullbackProjection h K) :=
  Functor.epi_conjQuotientProjection _ _

/-- The pullback of a quotient of `F_T` along a morphism `h : T' ⟶ T` of test schemes,
`Q ↦ (X_{T'} ⟶ X_T)^*Q`, recorded by its kernel. -/
@[stacks 082M "the pullback Q' = (X_{T'} ⟶ X_T)^*Q of a quotient of F_T along a morphism \
T' ⟶ T of test schemes over Y"]
def quotientPullback {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) : Subobject (D.baseChangeModule T') :=
  Functor.conjSubobject (D.baseChangeComparison h) K

/-- The pulled-back quotient is the inverse image of the quotient: the quotient of
`F_{T'}` by `quotientPullback h K` is `(X_{T'} ⟶ X_T)^*(F_T/K)`. -/
def quotientPullbackCokernelIso {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) :
    D.quotientModule T' (D.quotientPullback h K) ≅
      (modulePullback B S hS (D.relativeMap h)).obj (D.quotientModule T K) :=
  Functor.conjSubobjectCokernelIso (D.baseChangeComparison h) K

/-- The projection onto the quotient by the pulled-back subobject is the projection onto the
inverse image of the quotient. -/
theorem quotientProjection_comp_quotientPullbackCokernelIso_hom {T' T : SchemesOver D.Y}
    (h : T' ⟶ T) (K : Subobject (D.baseChangeModule T)) :
    D.quotientProjection T' (D.quotientPullback h K) ≫
        (D.quotientPullbackCokernelIso h K).hom = D.quotientPullbackProjection h K :=
  Functor.cokernel_π_comp_conjSubobjectCokernelIso_hom (D.baseChangeComparison h) K

/-- Pullback of quotients along the identity of a test scheme is the identity. -/
theorem quotientPullback_id (hc : ModulePushforwardCoherence B S hS) (T : SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) : D.quotientPullback (𝟙 T) K = K :=
  Functor.conjSubobject_id _ _ (D.baseChangeComparison_id hc T) K

/-- Pullback of quotients is compatible with composition of morphisms of test schemes. -/
theorem quotientPullback_comp (hc : ModulePushforwardCoherence B S hS)
    {T'' T' T : SchemesOver D.Y} (h : T'' ⟶ T') (k : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) :
    D.quotientPullback (h ≫ k) K = D.quotientPullback h (D.quotientPullback k K) :=
  Functor.conjSubobject_comp (D.baseChangeComparison k) (D.baseChangeComparison h)
    (D.baseChangeComparison (h ≫ k))
    (modulePullbackTriangle B S hS (baseChangeMap_comp D.f h k).symm)
    (D.baseChangeComparison_comp hc h k) K

/-! ### The conditions of the source under pullback -/

/-- The inverse image along `X_{T'} ⟶ X_T` of a quasi-coherent `𝒪_{X_T}`-module flat over `T` is
flat over `T'`. -/
def PullbackPreservesFlatOver : Prop :=
  ∀ {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (Q : Modules.{u, u} B S hS (D.space T).1 (D.space T).2),
      Q.IsQuasicoherentOnSite →
        IsFlatOver B S hS (D.space T).2 (D.projection T).hom Q →
          IsFlatOver B S hS (D.space T').2 (D.projection T').hom
            ((modulePullback B S hS (D.relativeMap h)).obj Q)

/-- The inverse image along `X_{T'} ⟶ X_T` of a quasi-coherent module flat over `T` is flat over
`T'`. -/
theorem pullbackPreservesFlatOver : D.PullbackPreservesFlatOver := by
  intro _ _ h Q hQ hflat
  have := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (D.relativeMap h) Q hQ
  exact isFlatOver_modulePullback B S hS (isPullback_baseChangeMap D.f h) Q hflat

/-- The inverse image along `X_{T'} ⟶ X_T` of a module of finite presentation is of finite
presentation. -/
def PullbackPreservesFinitePresentation : Prop :=
  ∀ {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (Q : Modules.{u, u} B S hS (D.space T).1 (D.space T).2),
      Q.IsFinitePresentationOnSite →
        ((modulePullback B S hS (D.relativeMap h)).obj Q).IsFinitePresentationOnSite

/-- The quotient by the pullback of a subobject in `Q_{F/X/Y}(T)` is flat over `T'`. -/
private theorem isFlatOver_quotientModule_quotientPullback {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (hK : K ∈ D.quotients T) :
    IsFlatOver B S hS (D.space T').2 (D.projection T').hom
      (D.quotientModule T' (D.quotientPullback h K)) :=
  IsFlatOver.of_iso B S hS (D.space T').2 (D.quotientPullbackCokernelIso h K).symm
    (D.pullbackPreservesFlatOver h (D.quotientModule T K) hK.1 hK.2)

/-- The pullback of a quotient of `F_T` which is quasi-coherent and flat over `T` is
quasi-coherent and flat over `T'`. -/
@[stacks 082M "the pullback clause: if F_T ⟶ Q is an element of Q_{F/X/Y}(T) and T' ⟶ T is a \
morphism of schemes over Y, then Q' = (X_{T'} ⟶ X_T)^*Q is a quasi-coherent 𝒪_{X_{T'}}-module \
flat over T', so it is an element of Q_{F/X/Y}(T')"]
theorem quotientPullback_mem_quotients' {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (hK : K ∈ D.quotients T) :
    D.quotientPullback h K ∈ D.quotients T' :=
  ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso (D.quotientPullbackCokernelIso h K).symm
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (D.relativeMap h) (D.quotientModule T K) hK.1),
    D.isFlatOver_quotientModule_quotientPullback h K hK⟩

/-- The pullback of a finitely presented quotient is a finitely presented quotient. -/
@[stacks 082M "Q^{fp}_{F/X/Y} is a subfunctor of Q_{F/X/Y}: finite presentation of a quotient \
is preserved by the pullback along a morphism of test schemes, so the finitely presented \
quotients are stable under the transition maps"]
theorem quotientPullback_mem_finitePresentationQuotients {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (hK : K ∈ D.finitePresentationQuotients T) :
    D.quotientPullback h K ∈ D.finitePresentationQuotients T' :=
  ⟨D.quotientPullback_mem_quotients' h K hK.1,
    SheafOfModules.IsFinitePresentationOnSite.of_iso (D.quotientPullbackCokernelIso h K).symm
      (isFinitePresentationOnSite_modulePullback B S hS (D.relativeMap h)
        (D.quotientModule T K) hK.2)⟩

/-! ### The conditions of the source under pullback of a finitely presented quotient -/

/-- The inverse image along `X_{T'} ⟶ X_T` of a module of finite presentation is of finite
presentation. -/
theorem pullbackPreservesFinitePresentation : D.PullbackPreservesFinitePresentation :=
  fun h Q hQ ↦ isFinitePresentationOnSite_modulePullback B S hS (D.relativeMap h) Q hQ

/-- The pullback of a quotient of `F_T` of finite presentation is of finite presentation. -/
theorem isFinitePresentationOnSite_quotientPullback {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (hK : K ∈ D.finitePresentationQuotients T) :
    (D.quotientModule T' (D.quotientPullback h K)).IsFinitePresentationOnSite :=
  SheafOfModules.IsFinitePresentationOnSite.of_iso (D.quotientPullbackCokernelIso h K).symm
    (D.pullbackPreservesFinitePresentation h (D.quotientModule T K) hK.2)

/-- The pullback of a quotient of `F_T` of finite presentation is quasi-coherent. -/
theorem isQuasicoherentOnSite_quotientPullback {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (hK : K ∈ D.finitePresentationQuotients T) :
    (D.quotientModule T' (D.quotientPullback h K)).IsQuasicoherentOnSite :=
  have := D.isFinitePresentationOnSite_quotientPullback h K hK
  inferInstance

/-- The pullback of a quotient of `F_T` of finite presentation which is flat over `T` is flat
over `T'`. -/
theorem isFlatOver_quotientPullback {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (hK : K ∈ D.finitePresentationQuotients T) :
    IsFlatOver B S hS (D.space T').2 (D.projection T').hom
      (D.quotientModule T' (D.quotientPullback h K)) :=
  D.isFlatOver_quotientModule_quotientPullback h K hK.1

/-! ### The functor of quotients -/

/-- The functor of quotients of `F/X/Y`,
`Q_{F/X/Y} : (Sch/Y)ᵒᵖ ⥤ Sets`: its value at a test scheme `T` over `Y` is the set
`Q_{F/X/Y}(T)` of quotients of `F_T` that are quasi-coherent and flat over `T`, and its action
on a morphism of test schemes is pullback of quotients. -/
@[stacks 082N "the functor of quotients Q_{F/X/Y} of F/X/Y, with its two functor laws and the \
stability of the quotients of the source under pullback along a morphism of test schemes",
  sga "3 XV 3.8" "more general"]
def quotientsFunctor : (SchemesOver D.Y)ᵒᵖ ⥤ Type (u + 1) where
  obj T := D.quotients T.unop
  map {_ _} m := ↾fun K ↦
    ⟨D.quotientPullback m.unop K.1,
      D.quotientPullback_mem_quotients' m.unop K.1 K.2⟩
  map_id T := congrArg TypeCat.ofHom (funext fun K ↦
    Subtype.ext (D.quotientPullback_id (modulePushforwardCoherence B S hS) T.unop K.1))
  map_comp m n := congrArg TypeCat.ofHom (funext fun K ↦
    Subtype.ext (D.quotientPullback_comp (modulePushforwardCoherence B S hS) n.unop m.unop K.1))

/-- The value of the functor of quotients at a test scheme `T` over `Y` is the set
`Q_{F/X/Y}(T)`. -/
@[stacks 082M "the functor Q_{F/X/Y} : (Sch/Y)ᵒᵖ ⥤ Sets obtained from the pullback clause, \
through its value at a test scheme T over Y, which is the set Q_{F/X/Y}(T)"]
theorem quotientsFunctor_obj (T : SchemesOver D.Y) :
    D.quotientsFunctor.obj (Opposite.op T) = D.quotients T :=
  rfl

/-- The action of the functor of quotients on a morphism of test schemes is
pullback of quotients. -/
@[stacks 082M "the functor Q_{F/X/Y} : (Sch/Y)ᵒᵖ ⥤ Sets obtained from the pullback clause, \
through its transition maps, which are the pullback Q ↦ (X_{T'} ⟶ X_T)^*Q of quotients"]
theorem quotientsFunctor_map {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (hK : K ∈ D.quotients T) :
    (D.quotientsFunctor.map (Opposite.op h)
      ⟨K, hK⟩ : D.quotients T').1 = D.quotientPullback h K :=
  rfl

/-- The finite-presentation subfunctor `Q^{fp}_{F/X/Y} : (Sch/Y)ᵒᵖ ⥤ Sets` of the functor of
quotients: its value at a test scheme `T` is the subset of `Q_{F/X/Y}(T)` of those quotients that
are of finite presentation as `𝒪_{X_T}`-modules, and its action on a morphism of test schemes is
pullback of quotients. -/
@[stacks 0CZL "the finite-presentation subfunctor Q^{fp}_{F/X/Y} of the functor of quotients"]
def finitePresentationQuotientsFunctor : (SchemesOver D.Y)ᵒᵖ ⥤ Type (u + 1) where
  obj T := D.finitePresentationQuotients T.unop
  map {_ _} m := ↾fun K ↦
    ⟨D.quotientPullback m.unop K.1,
      ⟨⟨D.isQuasicoherentOnSite_quotientPullback m.unop K.1 K.2,
        D.isFlatOver_quotientPullback m.unop K.1 K.2⟩,
        D.isFinitePresentationOnSite_quotientPullback m.unop K.1 K.2⟩⟩
  map_id T := congrArg TypeCat.ofHom (funext fun K ↦
    Subtype.ext (D.quotientPullback_id (modulePushforwardCoherence B S hS) T.unop K.1))
  map_comp m n := congrArg TypeCat.ofHom (funext fun K ↦
    Subtype.ext (D.quotientPullback_comp (modulePushforwardCoherence B S hS)
      n.unop m.unop K.1))

/-- The finite-presentation subfunctor is a subfunctor of the functor of
quotients: at every test scheme its value is a subset of the value of
`AlgebraicGeometry.Space.QuotientSituation.quotientsFunctor`, and the two actions agree. -/
@[stacks 082M "Q^{fp}_{F/X/Y} : (Sch/Y)ᵒᵖ ⥤ Sets is a subfunctor of Q_{F/X/Y}: the inclusion \
of the finitely presented quotients into all of them is a morphism of functors"]
def finitePresentationQuotientsFunctorToQuotientsFunctor :
    D.finitePresentationQuotientsFunctor ⟶ D.quotientsFunctor where
  app T := ↾fun K ↦ ⟨K.1, D.finitePresentationQuotients_subset_quotients T.unop K.2⟩

end QuotientSituation

end AlgebraicGeometry.Space

end
