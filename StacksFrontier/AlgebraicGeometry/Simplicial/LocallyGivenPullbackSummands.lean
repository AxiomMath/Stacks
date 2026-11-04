module

public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenSolution
public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenGlueing
public import StacksFrontier.AlgebraicGeometry.Simplicial.TotalRestrictionSummand
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullbackOfIsIsoFSharp
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedTransitionInduced
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.StructureAugmentationPullback

/-!
# The summands of `La^*F` are the restrictions of `F`

In Situation 0DC9, let `L` be a simplicial object of `SR(B)`, `K = u(L)`, and let
`a : ((C/K)_total, O) ⟶ (C, O_C)` be the ringed augmentation of Remark 0D9W with `O` the
restricted structure sheaf. For an object `F` of `D(O_C)` the restriction of `La^*F` to the
summand `C/u(U_{n,i})` of the degree-`n` component is `F|_{C/u(U_{n,i})}`, naturally in `F`, and
under these identifications the derived transitions of `La^*F` (Stacks 0D9P) are the
identifications `(F|_{u(U_{m,j})})|_{u(U_{n,i})} = F|_{u(U_{n,i})}`. Consequently a solution
`(F, ρ_U)` of the glueing problem gives an identification of the summandwise restrictions of
`La^*F` with the locally given objects, compatible with the `ρ_a`, in the sense of Stacks 0DCA.

## Main definitions

* `AlgebraicGeometry.RingedSite.LocallyGiven.structurePullback`: `La^*` for the ringed
  augmentation with the restricted structure sheaf.
* `AlgebraicGeometry.RingedSite.LocallyGiven.pullbackSummandIso`:
  `((La^*F)_n)|_{C/u(U_{n,i})} ≅ F|_{C/u(U_{n,i})}`.
* `AlgebraicGeometry.RingedSite.LocallyGiven.Solution.summandIdentification`: the summandwise
  identification of `La^*F` given by a solution `(F, ρ_U)`.

## Main results

* `AlgebraicGeometry.RingedSite.LocallyGiven.pullbackSummandIso_transition`: the derived
  transitions of `La^*F` are, summandwise, the restriction comparisons of `F`.

## References

* [Stacks Project, Tag 0DCA](https://stacks.math.columbia.edu/tag/0DCA)
* [Stacks Project, Tag 0DCB](https://stacks.math.columbia.edu/tag/0DCB)
* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SimplicialSemiRepresentable Stacks.CategoryTheory.Hypercovering

universe u uB vB

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent
  RingedToposHom.pullbackModules_preservesFiniteLimits_of_isIso_fSharp
  RingedToposHom.pullbackModules_preservesFiniteColimits_of_adjunction
  RingedSite.overFunctor_preservesFiniteLimits' RingedSite.overFunctor_preservesFiniteColimits'

namespace CategoryTheory

/-- Transport of a transition compatibility along an isomorphism `ζ : R ≅ R'` of the first
functor. -/
theorem transition_restriction_of_iso {MC MT Mm Mn MUn MUm : Type*} [Category MC] [Category MT]
    [Category Mm] [Category Mn] [Category MUn] [Category MUm]
    (R R' : MC ⥤ MT) (Cm : MT ⥤ Mm) (Cn : MT ⥤ Mn) (P : Mm ⥤ Mn) (Sn : Mn ⥤ MUn)
    (Sm : Mm ⥤ MUm) (M : MUm ⥤ MUn) (OU : MC ⥤ MUn) (OU' : MC ⥤ MUm) (ζ : R ≅ R')
    (τ : Cm ⋙ P ⟶ Cn) (θn : R' ⋙ Cn ⋙ Sn ≅ OU) (θm : R' ⋙ Cm ⋙ Sm ≅ OU')
    (π : P ⋙ Sn ≅ Sm ⋙ M) (ω : OU' ⋙ M ≅ OU)
    (h : ∀ X : MC, Sn.map (τ.app (R'.obj X)) ≫ θn.hom.app X =
      π.hom.app (Cm.obj (R'.obj X)) ≫ M.map (θm.hom.app X) ≫ ω.hom.app X) (X : MC) :
    Sn.map (τ.app (R.obj X)) ≫ (Functor.isoWhiskerRight ζ (Cn ⋙ Sn) ≪≫ θn).hom.app X =
      π.hom.app (Cm.obj (R.obj X)) ≫
        M.map ((Functor.isoWhiskerRight ζ (Cm ⋙ Sm) ≪≫ θm).hom.app X) ≫ ω.hom.app X := by
  have hτ := τ.naturality (ζ.hom.app X)
  have hπ := π.hom.naturality (Cm.map (ζ.hom.app X))
  simp only [Functor.comp_map] at hτ hπ
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, ← hτ, Functor.map_comp_assoc, h, ← Category.assoc,
    hπ, Category.assoc]

end CategoryTheory

namespace AlgebraicGeometry.RingedSite.LocallyGiven

attribute [local instance] LocallyGiven.category

/-- Sheafification is available in any module universe containing the site. -/
local instance (priority := 100) pullbackSummandsSheafification.{uM, w, v}
    {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{w, uM}] [UnivLE.{v, uM}] : HasSheafify J AddCommGrpCat.{uM} :=
  hasSheafifyEssentiallySmallSite.{v, uM, w, uM + 1, uM} J _

/-- In the module universe, sheafification equivalences are the locally bijective maps. -/
local instance (priority := 100) pullbackSummandsLocallyBijective.{uM, w, v}
    {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{w, uM}] [UnivLE.{v, uM}] : J.WEqualsLocallyBijective AddCommGrpCat.{uM} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, uM, w, uM + 1, uM} J

variable {X : RingedSite.{u, u, u}} [X.J.toCoverage.HasPullbacks]
  (G : LocallyGiven.{0, u, u, u, uB, vB} X) (L : SimplicialObject (FormalCoproduct.{u} G.B))

/-- The ringed augmentation `a : ((C/K)_total, O) ⟶ (C, O_C)` of Remark 0D9W for `K = u(L)`, with
`O` the restricted structure sheaf. -/
abbrev augmentationHom :=
  (structureAugmentation X (G.image L)).totalRingedHom

/-- **`La^*`** along the ringed augmentation with the restricted structure sheaf. -/
abbrev structurePullback :=
  (RingedToposHom.leftDerivedPullbackOfIsIsoFSharp (G.augmentationHom L)).functor

/-- The pullback `a^*` of sheaves of modules, with values in the modules over the restricted
structure sheaf of the total site. -/
def structurePullbackModules :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      ((situation X.J (G.image L)).totalRingedTopos (structureSheaf X (G.image L))).Modules :=
  (G.augmentationHom L).toModulesHom.pullbackModules

/-- The pullback `a^*` of sheaves of modules is additive. -/
instance : (G.structurePullbackModules L).Additive :=
  inferInstanceAs (G.augmentationHom L).toModulesHom.pullbackModules.Additive

/-- The pullback `a^*` of sheaves of modules preserves finite limits. -/
instance : PreservesFiniteLimits (G.structurePullbackModules L) :=
  inferInstanceAs (PreservesFiniteLimits (G.augmentationHom L).toModulesHom.pullbackModules)

/-- The pullback `a^*` of sheaves of modules preserves finite colimits. -/
instance : PreservesFiniteColimits (G.structurePullbackModules L) :=
  inferInstanceAs (PreservesFiniteColimits (G.augmentationHom L).toModulesHom.pullbackModules)

/-- `La^*` is the functor induced by the exact pullback `a^*` on derived categories. -/
def structurePullbackIso :
    G.structurePullback L ≅ (G.structurePullbackModules L).mapDerivedCategory :=
  RingedToposHom.derivedPullbackNatIsoOfIsIsoFSharp (G.augmentationHom L)

/-- The identification of the sheaf-level composite `a^*`, restriction to the degree-`n`
component, restriction to the summand `C/u(U_{n,i})`, with restriction to the slice. -/
def pullbackSummandIsoUnderived (n : SimplexCategory) (i : (L.obj (op n)).I) :
    G.structurePullbackModules L ⋙
        (situation X.J (G.image L)).componentModulesRestriction (structureSheaf X (G.image L)) n ⋙
          G.summandRestrictionB L n i ≅
      SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (G.u.obj ((L.obj (op n)).obj i)) :=
  Functor.isoWhiskerRight (structurePullbackModulesRestrictionIso X (G.image L)) _ ≪≫
    totalRestrictionSummandIso X (G.image L) n i

/-- The derived form of `pullbackSummandIsoUnderived`, for the exact `a^*`. -/
def pullbackSummandIso' (n : SimplexCategory) (i : (L.obj (op n)).I) :
    (G.structurePullbackModules L).mapDerivedCategory ⋙
        (situation X.J (G.image L)).derivedComponentModuleRestriction
          (structureSheaf X (G.image L)) n ⋙ G.summandDerivedRestriction L n i ≅
      derivedOverFunctor X (G.u.obj ((L.obj (op n)).obj i)) :=
  CategoryTheory.derivedRestrictionIso (G.structurePullbackModules L)
    ((situation X.J (G.image L)).componentModulesRestriction (structureSheaf X (G.image L)) n)
    (G.summandRestrictionB L n i)
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (G.u.obj ((L.obj (op n)).obj i)))
    (G.pullbackSummandIsoUnderived L n i)

/-- **`((La^*F)_n)|_{C/u(U_{n,i})} ≅ F|_{C/u(U_{n,i})}`**, naturally in `F`. -/
def pullbackSummandIso (n : SimplexCategory) (i : (L.obj (op n)).I) :
    G.structurePullback L ⋙
        (situation X.J (G.image L)).derivedComponentModuleRestriction
          (structureSheaf X (G.image L)) n ⋙ G.summandDerivedRestriction L n i ≅
      derivedOverFunctor X (G.u.obj ((L.obj (op n)).obj i)) :=
  Functor.isoWhiskerRight (G.structurePullbackIso L) _ ≪≫ G.pullbackSummandIso' L n i

/-- **On sheaves, the transitions of `a^*N` are the restriction comparisons of `N`**, under the
identifications `pullbackSummandIsoUnderived`. -/
theorem pullbackSummandIsoUnderived_transition {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I) (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (G.summandRestrictionB L n i).map
        (((situation X.J (G.image L)).componentModulesTransition (structureSheaf X (G.image L))
          φ).app ((G.structurePullbackModules L).obj N)) ≫
        (G.pullbackSummandIsoUnderived L n i).hom.app N =
      (G.summandPullbackIso L φ i).hom.app
          (((situation X.J (G.image L)).componentModulesRestriction (structureSheaf X (G.image L))
            m).obj ((G.structurePullbackModules L).obj N)) ≫
        (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (G.u.map ((L.map φ.op).φ i))).map
            ((G.pullbackSummandIsoUnderived L m ((L.map φ.op).f i)).hom.app N) ≫
          (SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (G.u.map ((L.map φ.op).φ i))).hom.app N :=
  CategoryTheory.transition_restriction_of_iso (G.structurePullbackModules L)
    (totalRestriction X (G.image L))
    ((situation X.J (G.image L)).componentModulesRestriction (structureSheaf X (G.image L)) m)
    ((situation X.J (G.image L)).componentModulesRestriction (structureSheaf X (G.image L)) n)
    (G.transitionPullback L φ) (G.summandRestrictionB L n i)
    (G.summandRestrictionB L m ((L.map φ.op).f i))
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (G.u.map ((L.map φ.op).φ i)))
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (G.u.obj ((L.obj (op n)).obj i)))
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (G.u.obj ((L.obj (op m)).obj ((L.map φ.op).f i))))
    (structurePullbackModulesRestrictionIso X (G.image L))
    ((situation X.J (G.image L)).componentModulesTransition (structureSheaf X (G.image L)) φ)
    (totalRestrictionSummandIso X (G.image L) n i)
    (totalRestrictionSummandIso X (G.image L) m ((L.map φ.op).f i))
    (G.summandPullbackIso L φ i)
    (SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (G.u.map ((L.map φ.op).φ i)))
    (fun N ↦ totalRestriction_summand_transition X (G.image L) φ i N) N

/-- **The derived transitions of `a^*F` are the restriction comparisons of `F`**, under the
identifications `pullbackSummandIso'`. -/
theorem pullbackSummandIso'_transition {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I)
    (N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (G.summandDerivedRestriction L n i).map
        (((situation X.J (G.image L)).derivedComponentModuleTransition
          (structureSheaf X (G.image L)) φ).app
            ((G.structurePullbackModules L).mapDerivedCategory.obj N)) ≫
        (G.pullbackSummandIso' L n i).hom.app N =
      (G.summandDerivedPullbackIso L φ i).hom.app
          (((situation X.J (G.image L)).derivedComponentModuleRestriction
            (structureSheaf X (G.image L)) m).obj
              ((G.structurePullbackModules L).mapDerivedCategory.obj N)) ≫
        (G.restriction ((L.map φ.op).φ i)).map
          ((G.pullbackSummandIso' L m ((L.map φ.op).f i)).hom.app N) ≫
          (derivedOverFunctorMapIso X (G.u.map ((L.map φ.op).φ i))).hom.app N :=
  let := (situation X.J (G.image L)).transitionPullbackModules_preservesFiniteLimits
    (structureSheaf X (G.image L)) φ (transitionRingedToposHom_isFlat X (G.image L) φ)
  let := G.restrictionAdditive ((L.map φ.op).φ i)
  have := overMap_preservesFiniteLimits.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (G.u.map ((L.map φ.op).φ i))
  have := overMap_preservesFiniteColimits.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (G.u.map ((L.map φ.op).φ i))
  CategoryTheory.derived_transition_restriction_compat (G.structurePullbackModules L)
    ((situation X.J (G.image L)).componentModulesRestriction (structureSheaf X (G.image L)) m)
    ((situation X.J (G.image L)).componentModulesRestriction (structureSheaf X (G.image L)) n)
    (G.transitionPullback L φ) (G.summandRestrictionB L n i)
    (G.summandRestrictionB L m ((L.map φ.op).f i))
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (G.u.map ((L.map φ.op).φ i)))
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (G.u.obj ((L.obj (op n)).obj i)))
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (G.u.obj ((L.obj (op m)).obj ((L.map φ.op).f i))))
    ((situation X.J (G.image L)).componentModulesTransition (structureSheaf X (G.image L)) φ)
    (G.pullbackSummandIsoUnderived L n i) (G.pullbackSummandIsoUnderived L m ((L.map φ.op).f i))
    (G.summandPullbackIso L φ i)
    (SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (G.u.map ((L.map φ.op).φ i)))
    ((situation X.J (G.image L)).derivedTransitionPullback (structureSheaf X (G.image L)) φ)
    ((situation X.J (G.image L)).derivedTransitionComparison (structureSheaf X (G.image L)) φ)
    (G.pullbackSummandIsoUnderived_transition L φ i) N

/-- **The derived transitions of `La^*F` are, summandwise, the restriction comparisons of `F`**:
under the identifications `((La^*F)_n)|_{C/u(U_{n,i})} ≅ F|_{C/u(U_{n,i})}`, the transition of
`La^*F` along `φ : [m] ⟶ [n]`, read on the `i`-th summand, is the comparison
`(F|_{u(U_{m,j})})|_{u(U_{n,i})} = F|_{u(U_{n,i})}` along the arrow `U_{n,i} ⟶ U_{m,j}` of
`L(φ)`. -/
theorem pullbackSummandIso_transition {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (L.obj (op n)).I)
    (N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (G.summandDerivedRestriction L n i).map
        (((situation X.J (G.image L)).derivedComponentModuleTransition
          (structureSheaf X (G.image L)) φ).app ((G.structurePullback L).obj N)) ≫
        (G.pullbackSummandIso L n i).hom.app N =
      (G.summandDerivedPullbackIso L φ i).hom.app
          (((situation X.J (G.image L)).derivedComponentModuleRestriction
            (structureSheaf X (G.image L)) m).obj ((G.structurePullback L).obj N)) ≫
        (G.restriction ((L.map φ.op).φ i)).map
          ((G.pullbackSummandIso L m ((L.map φ.op).f i)).hom.app N) ≫
          (derivedOverFunctorMapIso X (G.u.map ((L.map φ.op).φ i))).hom.app N :=
  CategoryTheory.transition_restriction_of_iso (G.structurePullback L)
    (G.structurePullbackModules L).mapDerivedCategory
    ((situation X.J (G.image L)).derivedComponentModuleRestriction (structureSheaf X (G.image L)) m)
    ((situation X.J (G.image L)).derivedComponentModuleRestriction (structureSheaf X (G.image L)) n)
    ((situation X.J (G.image L)).derivedTransitionPullback (structureSheaf X (G.image L)) φ)
    (G.summandDerivedRestriction L n i) (G.summandDerivedRestriction L m ((L.map φ.op).f i))
    (G.restriction ((L.map φ.op).φ i)) (derivedOverFunctor X (G.u.obj ((L.obj (op n)).obj i)))
    (derivedOverFunctor X (G.u.obj ((L.obj (op m)).obj ((L.map φ.op).f i))))
    (G.structurePullbackIso L)
    ((situation X.J (G.image L)).derivedComponentModuleTransition (structureSheaf X (G.image L)) φ)
    (G.pullbackSummandIso' L n i) (G.pullbackSummandIso' L m ((L.map φ.op).f i))
    (G.summandDerivedPullbackIso L φ i) (derivedOverFunctorMapIso X (G.u.map ((L.map φ.op).φ i)))
    (G.pullbackSummandIso'_transition L φ i) N

variable {G} in
/-- **A solution of the glueing problem identifies the summands of `La^*F` with the locally
given objects, compatibly with the `ρ_a`**: the identification `((La^*F)_n)|_{C/u(U_{n,i})} ≅
F|_{C/u(U_{n,i})} ≅ E_{U_{n,i}}`, the second map being `ρ_{U_{n,i}}`. -/
def Solution.summandIdentification (S : G.Solution) :
    G.SummandIdentification L ((G.structurePullback L).obj S.obj) where
  iso n i := (G.pullbackSummandIso L n i).app S.obj ≪≫ S.iso ((L.obj (op n)).obj i)
  comm {m n} φ i := by
    have h := G.pullbackSummandIso_transition L φ i S.obj
    have hS := S.comm ((L.map φ.op).φ i)
    change (G.summandDerivedRestriction L n i).map
        (((situation X.J (G.image L)).derivedComponentModuleTransition
          (structureSheaf X (G.image L)) φ).app ((G.structurePullback L).obj S.obj)) ≫
        (G.pullbackSummandIso L n i).hom.app S.obj ≫ (S.iso ((L.obj (op n)).obj i)).hom = _
    rw [← Category.assoc, h, Category.assoc, Category.assoc, ← hS, Iso.hom_inv_id_app_assoc]
    refine congrArg (_ ≫ ·) ?_
    rw [← Category.assoc, ← Functor.map_comp]
    rfl

end AlgebraicGeometry.RingedSite.LocallyGiven

end
