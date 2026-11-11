module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforward
import StacksCore.Tactic.StacksAttribute

/-!
# Derived objects supported on the complement of the open subspace of an elementary square

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, let `P = U ×_X V` be its intersection and set `T = |X| \ |U|`.  Stacks 08GG says
that

1. an object `E` of `D(𝒪_X)` supported on `T` satisfies (a) `E ⟶ Rj_*(E|_V)` and (b)
   `j_!(E|_V) ⟶ E` are isomorphisms, and
2. an object `F` of `D(𝒪_V)` supported on `j^{-1}T` satisfies (a) `F ⟶ (j_!F)|_V`, (b)
   `(Rj_*F)|_V ⟶ F` and (c) `j_!F ⟶ Rj_*F` are isomorphisms.

Part (1) is the source's own two-line deduction from the two Mayer–Vietoris statements of the
section: `E` supported on `T` has `E|_U = 0` and `E|_P = 0`, so in the extension-by-zero
triangle of Stacks 08GV part (2) the first term and the `U`-summand of the second vanish, and
in the direct-image triangle of Stacks 08GW part (2) the third term and the `U`-summand of the
second vanish.  Both deductions are carried out below.

For part (2) this file proves the passage from clauses (a) and (b), and from clause (1)(a) at
the two objects `j_!F` and `Rj_*F`, to clause (c).

The deductions here take their inputs (the Mayer–Vietoris statements, the vanishing of the
restrictions of a supported object, the other clauses) as explicit arguments.  All of those
inputs are theorems of the library, and every clause of Stacks 08GG is proved unconditionally,
and registered, in `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/SupportedOnComplementClauses.lean`
(see `AlgebraicGeometry.Space.isIso_of_cohomologySupportedOn_edsEtale` there for all five
clauses together), in `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/SupportedExtensionByZero.lean`
and in `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/SupportedPushforwardPerfect.lean`.

## Main definitions

* `AlgebraicGeometry.Space.edsComplementPoints` is the set `T = |X| \ |U|` of points, the
  complement of the range of the map on points of the inclusion of the open subspace.  It is
  the set whose reduced closed subspace the last field of
  `AlgebraicGeometry.Space.IsElementaryDistinguishedSquare` refers to.
* `AlgebraicGeometry.Space.supportedShriekToPushforward` is the comparison `j_!F ⟶ Rj_*F` of
  clause (2)(c), namely the adjunct under `(-)|_V ⊣ Rj_*` of the inverse of the unit
  `F ⟶ (j_!F)|_V` of clause (2)(a).

## Main results

* `CategoryTheory.Adjunction.isIso_homEquiv_inv_unit`: for a triple of adjoint functors
  `L ⊣ M ⊣ R` and an object `F` at which the unit of `L ⊣ M`, the counit of `M ⊣ R` and the
  unit of `M ⊣ R` at `L F` and at `R F` are all invertible, the comparison `L F ⟶ R F`
  adjunct to the inverse of the first is invertible.  This is the formal content of the
  passage from clauses (2)(a), (2)(b) and (1)(a) to clause (2)(c).
* `AlgebraicGeometry.Space.isIso_counit_mapDerivedCategory_of_cohomologySupportedOn`: the
  deduction of clause (1)(b) of Stacks 08GG from part (1) of Stacks 08GV and the vanishing of
  the restrictions to `U` and to `P`.
* `AlgebraicGeometry.Space.exists_isIso_derivedRestrictPush_of_cohomologySupportedOn`: the
  deduction from Stacks 08GW part (2) that an object supported on `T` is isomorphic to
  `Rj_*(E|_V)`.
* `AlgebraicGeometry.Space.isIso_supportedShriekToPushforward`: the deduction of clause (2)(c)
  from clauses (2)(a), (2)(b) and (1)(a).

## Implementation notes

*The support predicate.*  "Supported on `T`" is
`AlgebraicGeometry.Space.CohomologySupportedOn` of Stacks 08GF, which asks that every
cohomology sheaf `Hⁱ(E)` have `AlgebraicGeometry.Space.supportOfSheaf` contained in `T`.  No
new predicate is introduced.

*The restriction vanishings.*  The source passes from "`E` is supported on `T`" to
"`E|_U = 0`" by `Hⁱ(E|_U) = Hⁱ(E)|_U` and the vanishing of a sheaf with empty support, Stacks
04K5.  The deductions here take that implication as the argument `hvan`, stated for every
étale morphism whose points land in `|U|`; it is a theorem of the library,
`AlgebraicGeometry.Space.isZero_etaleModulePullback_mapDerivedCategory_of_range_subset`.
Applying `hvan` to the open immersion and to the morphism out of the intersection gives exactly
the source's `E|_U = 0` and `E|_P = 0`; the containment of point sets is immediate for the
first and is functoriality of `AlgebraicGeometry.Space.pointsMap` for the second.

*Why clause (1)(a) is existential.*  `AlgebraicGeometry.Space.`
`exists_mem_distTriang_edsDerivedRestrictPushMayerVietoris`, the library's Stacks 08GW
part (2), quantifies the four maps of its triangle existentially, as the source does; the
canonical derived unit `E ⟶ Rj_{V,*}(E|_V)` is the map its proof term constructs but is not
exposed by its statement.  So what is proved here is that *some* map `E ⟶ Rj_{V,*}(E|_V)` is
an isomorphism, that is `E ≅ Rj_{V,*}(E|_V)`.  The statement about the canonical unit is
`AlgebraicGeometry.Space.isIso_derivedUnit_edsDerivedRestrictPushEtale_of_cohomologySupportedOn`
(at the chosen total right derived functors) and
`AlgebraicGeometry.Space.isIso_unit_derivedRestrict_of_cohomologySupportedOn` (at any right
adjoint of derived restriction).

*The derived direct images of a vanishing restriction.*  `R_U` and `R_P` are right derived
functors of the composites `j_{Y,*}((-)|_Y)`, not of `j_{Y,*}` alone, so `R_U E = 0` does not
follow formally from `E|_U = 0`; the source's step uses that restriction needs no derivation,
which is `AlgebraicGeometry.Space.isIso_etaleModulePullback_derivedUnit` together with the
composition of derived functors of Stacks 08GE.  The deduction here takes the two vanishings as
the arguments `hRUzero` and `hRPzero`, stated as implications from the restriction vanishings
that `hvan` produces; at the chosen total right derived functors they are
`AlgebraicGeometry.Space.isZero_totalRightDerived_etaleRestrictPush_of_isZero`.

*Extension by zero and the derived adjunctions enter as data*, exactly as in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/MayerVietoris.lean` and in Stacks 08HA: a
functor together with an adjunction exhibiting it as an adjoint of restriction determines the
functor up to a unique compatible isomorphism, so it pins both `j_!` and `Rj_*` and all four
of the unit and counit maps that the clauses of the source are about.  For clause (2)(c) the
adjunctions are taken on the unbounded derived categories, which is where the source's
comparison `j_!F ⟶ Rj_*F` lives; the source asserts it only for supported `F`, and indeed a
normalized comparison on all of `D(𝒪_V)` need not exist for a nonseparated étale `j`.

*Clauses (2)(a) and (2)(b).*  The source proves them by a base change of the square to `V`,
where `j` acquires a section.  The library proves them without that reduction:
`j_!F` is supported on `T` (Stacks 08HA), so clause (1)(b) at `j_!F`, the triangle identity
and the conservativity of `j_!` give clause (2)(a), and clause (1)(a) at `j_!F` then gives
clause (2)(b); see `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/SupportedOnComplementClauses.lean`.

## References

* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
* [Stacks Project, Tag 08GM](https://stacks.math.columbia.edu/tag/08GM)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 08HA](https://stacks.math.columbia.edu/tag/08HA)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Adjunction

/-- Let `L ⊣ M ⊣ R` be a triple of adjoint functors, `M : C ⥤ D` and `L, R : D ⥤ C`, and let
`F` be an object of `D`.  The adjunct, under `M ⊣ R`, of the inverse of the unit
`F ⟶ M(L F)` of `L ⊣ M` is a map `φ : L F ⟶ R F`.  If moreover the counit `M(R F) ⟶ F` of
`M ⊣ R` is invertible and so are the units `L F ⟶ R(M(L F))` and `R F ⟶ R(M(R F))` of
`M ⊣ R`, then `φ` is invertible.

Indeed `M φ` composed with the counit is the inverse of the unit of `L ⊣ M`, so `M φ` is
invertible; naturality of the unit of `M ⊣ R` at `φ` then exhibits `φ` as a composite of
three invertible maps. -/
theorem isIso_homEquiv_inv_unit {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {M : C ⥤ D} {L R : D ⥤ C} (adjL : L ⊣ M) (adjR : M ⊣ R) (F : D)
    [IsIso (adjL.unit.app F)] [IsIso (adjR.counit.app F)]
    [IsIso (adjR.unit.app (L.obj F))] [IsIso (adjR.unit.app (R.obj F))] :
    IsIso (adjR.homEquiv (L.obj F) F (inv (adjL.unit.app F))) := by
  set φ := adjR.homEquiv (L.obj F) F (inv (adjL.unit.app F)) with hφ
  have key : M.map φ ≫ adjR.counit.app F = inv (adjL.unit.app F) := by
    rw [hφ]
    exact (adjR.homEquiv (L.obj F) F).symm_apply_apply _
  have hM : IsIso (M.map φ) := by
    have h : M.map φ = inv (adjL.unit.app F) ≫ inv (adjR.counit.app F) := by
      rw [← key, assoc, IsIso.hom_inv_id, comp_id]
    rw [h]
    infer_instance
  have hnat : φ ≫ adjR.unit.app (R.obj F) = adjR.unit.app (L.obj F) ≫ R.map (M.map φ) :=
    adjR.unit.naturality φ
  have hφ' : φ = adjR.unit.app (L.obj F) ≫ R.map (M.map φ) ≫
      inv (adjR.unit.app (R.obj F)) := by
    rw [← assoc, ← hnat, assoc, IsIso.hom_inv_id, comp_id]
  have h2 : IsIso (adjR.unit.app (L.obj F) ≫ R.map (M.map φ) ≫
    inv (adjR.unit.app (R.obj F))) := inferInstance
  rwa [← hφ'] at h2

end CategoryTheory.Adjunction

namespace CategoryTheory.Limits

/-- The inclusion of the second summand of a binary biproduct whose first summand is a zero
object is an isomorphism: its inverse is the second projection, by the Pierce decomposition
`biprod.total` and the vanishing of the first projection. -/
theorem isIso_biprod_inr_of_isZero_fst {C : Type u₁} [Category.{v₁} C] [Preadditive C] (X Y : C)
    [HasBinaryBiproduct X Y] (hX : IsZero X) : IsIso (biprod.inr : Y ⟶ X ⊞ Y) := by
  refine ⟨biprod.snd, biprod.inr_snd, ?_⟩
  have h0 : (biprod.fst : X ⊞ Y ⟶ X) = 0 := hX.eq_of_tgt _ _
  rw [← biprod.total, h0, zero_comp, zero_add]

/-- The projection onto the second summand of a binary biproduct whose first summand is a zero
object is an isomorphism: its inverse is the inclusion of the second summand. -/
theorem isIso_biprod_snd_of_isZero_fst {C : Type u₁} [Category.{v₁} C] [Preadditive C] (X Y : C)
    [HasBinaryBiproduct X Y] (hX : IsZero X) : IsIso (biprod.snd : X ⊞ Y ⟶ Y) := by
  have := isIso_biprod_inr_of_isZero_fst X Y hX
  have : IsIso ((biprod.inr : Y ⟶ X ⊞ Y) ≫ biprod.snd) := by
    rw [biprod.inr_snd]
    infer_instance
  exact IsIso.of_isIso_comp_left (biprod.inr : Y ⟶ X ⊞ Y) biprod.snd

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- The set `T = |X| \ |U|` of points of an algebraic space `X` outside an open subspace `U`:
the complement of the range of the map on points of the inclusion `U.ι`.

This is the set on which the last field of
`AlgebraicGeometry.Space.IsElementaryDistinguishedSquare` asks the étale morphism of the
square to be an isomorphism, and it is the `T` of Stacks 08GG. -/
def edsComplementPoints {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Uo : Subfunctor X) :
    Set (points B S hS X) :=
  (Set.range (pointsMap B S hS Uo.toFunctor Uo.ι))ᶜ

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The points of the open subspace of an elementary distinguished square are exactly the
points of `W` outside `T = |W| \ |U|`: the map on points of `AlgebraicGeometry.Space.edsOpenHom`
is the map on points of the inclusion `U.ι`. -/
theorem range_pointsMap_edsOpenHom :
    Set.range (pointsMap B S hS (edsOpen B S hS hsq).1 (edsOpenHom B S hS hsq).hom) =
      Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) :=
  rfl

/-- The points of the intersection `U ×_W V` of an elementary distinguished square land in the
open subspace: its morphism to `W` factors through the open immersion by definition, and the
map on points of a composite is the composite of the maps on points. -/
theorem range_pointsMap_edsInterHom_subset :
    Set.range (pointsMap B S hS (edsInter B S hS hsq).1 (edsInterHom B S hS hsq).hom) ⊆
      Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) := by
  have h : (edsInterHom B S hS hsq).hom =
      (edsFst B S hS hsq).hom ≫ (edsOpenHom B S hS hsq).hom := rfl
  rw [h, pointsMap_comp]
  exact Set.range_comp_subset_range _ _

end Square

section ExtensionByZero

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjU : shriekU ⊣ etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq))
  (adjV : shriekV ⊣ etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq))
  (adjP : shriekP ⊣ etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq))
  [shriekU.Additive] [PreservesFiniteLimits shriekU] [PreservesFiniteColimits shriekU]
  [shriekV.Additive] [PreservesFiniteLimits shriekV] [PreservesFiniteColimits shriekV]
  [shriekP.Additive] [PreservesFiniteLimits shriekP] [PreservesFiniteColimits shriekP]

/-- The extension by zero of the restriction of a derived object whose restriction vanishes
itself vanishes: the derived functor of the composite is the composite of the derived
functors, and the derived functor of an exact functor is triangulated, hence additive. -/
theorem isZero_mapDerivedCategory_comp_of_isZero
    {Y : AlgebraicSpaces B S hS} (g : Y ⟶ W) (hg : IsEtale B S hS g.hom)
    (shriek : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS W.1 W.2)
    [shriek.Additive] [PreservesFiniteLimits shriek] [PreservesFiniteColimits shriek]
    [HasSheafify (smallEtaleRingedSite B S hS Y.1 Y.2).J AddCommGrpCat.{u}]
    [(smallEtaleRingedSite B S hS Y.1 Y.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : IsZero ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E)) :
    IsZero ((etaleModulePullback.{u, u} B S hS g hg ⋙ shriek).mapDerivedCategory.obj E) :=
  IsZero.of_iso (shriek.mapDerivedCategory.map_isZero hE)
    ((Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS g hg) shriek).app E)

/-- **The deduction of clause (1)(b) of Stacks 08GG from Mayer–Vietoris.**  Let
`(U ⊆ X, j : V ⟶ X)` be an elementary distinguished
square of algebraic spaces over a scheme `S`, let `P = U ×_X V` and set `T = |X| \ |U|`.  Let
`E` be an object of `D(𝒪_X)` supported on `T`.  Then the canonical map `j_!(E|_V) ⟶ E`, the
derived counit of the adjunction `j_! ⊣ (-)|_V`, is an isomorphism.

This is the source's own argument.  Stacks 08GV part (2) puts `E` in a distinguished triangle

`j_{P!}E|_P ⟶ j_{U!}E|_U ⊕ j_{V!}E|_V ⟶ E ⟶ (j_{P!}E|_P)[1]`;

support on `T` makes `E|_U` and `E|_P` vanish, hence also their extensions by zero, so the
first term of the triangle vanishes — whence the second map is an isomorphism — and the
`U`-summand of the second term vanishes, so the inclusion of the `V`-summand is an
isomorphism.  The composite of the two is the derived counit. -/
theorem isIso_counit_mapDerivedCategory_of_cohomologySupportedOn
    (a : etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq) ⋙ shriekP ⟶
        etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq) ⋙ shriekU)
    (b : etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq) ⋙ shriekP ⟶
        etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq) ⋙ shriekV)
    (hzero : ∀ F, biprod.lift (a.app F) (-(b.app F)) ≫
      biprod.desc (adjU.counit.app F) (adjV.counit.app F) = 0)
    (hMV : ∀ F, (ShortComplex.mk (biprod.lift (a.app F) (-(b.app F)))
      (biprod.desc (adjU.counit.app F) (adjV.counit.app F)) (hzero F)).ShortExact)
    [HasSheafify (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2).J AddCommGrpCat.{u}]
    [(smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
      (edsOpen B S hS hsq).2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify (smallEtaleRingedSite B S hS (edsInter B S hS hsq).1
      (edsInter B S hS hsq).2).J AddCommGrpCat.{u}]
    [(smallEtaleRingedSite B S hS (edsInter B S hS hsq).1
      (edsInter B S hS hsq).2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) E)
    (hvan : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) E →
      ∀ {Y : AlgebraicSpaces B S hS} (g : Y ⟶ W) (hg : IsEtale B S hS g.hom),
        Set.range (pointsMap B S hS Y.1 g.hom) ⊆
            Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) →
          IsZero ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E)) :
    IsIso ((NatTrans.mapDerivedCategory adjV.counit).app E) := by
  obtain ⟨δ, hδ⟩ := mem_distTriang_mayerVietoris B S hS hsq adjU adjV a b hzero hMV E
  have hU : IsZero ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E) :=
    hvan hE (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
      (range_pointsMap_edsOpenHom B S hS hsq).subset
  have hP : IsZero ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E) :=
    hvan hE (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)
      (range_pointsMap_edsInterHom_subset B S hS hsq)
  have hUz := isZero_mapDerivedCategory_comp_of_isZero B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq) shriekU E hU
  have hPz := isZero_mapDerivedCategory_comp_of_isZero B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq) shriekP E hP
  have hcomp : IsIso (biprod.desc
        ((NatTrans.mapDerivedCategory adjU.counit).app E)
        ((NatTrans.mapDerivedCategory adjV.counit).app E) ≫
      (Functor.mapDerivedCategoryIdIso
        (Modules.{u, u} B S hS W.1 W.2)).hom.app E) :=
    (Triangle.isZero₁_iff_isIso₂ _ hδ).1 hPz
  have hinr := isIso_biprod_inr_of_isZero_fst
    ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq) ⋙ shriekU).mapDerivedCategory.obj E)
    ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq) ⋙ shriekV).mapDerivedCategory.obj E) hUz
  rw [← biprod.inr_desc ((NatTrans.mapDerivedCategory adjU.counit).app E)
    ((NatTrans.mapDerivedCategory adjV.counit).app E)]
  have hdesc := IsIso.of_isIso_comp_right (biprod.desc
    ((NatTrans.mapDerivedCategory adjU.counit).app E)
    ((NatTrans.mapDerivedCategory adjV.counit).app E))
    ((Functor.mapDerivedCategoryIdIso (Modules.{u, u} B S hS W.1 W.2)).hom.app E)
  infer_instance

end ExtensionByZero

section Pushforward

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The deduction from Mayer–Vietoris of Stacks 08GG, clause (1)(a)**, in the existentially
quantified form that the library's
Stacks 08GW part (2) permits.  Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square
of algebraic spaces over a scheme `S`, let `P = U ×_X V` and set `T = |X| \ |U|`.  Let `R_U`,
`R_V` and `R_P` be right derived functors of the three composites `j_{Y,*}((-)|_Y)`, and
suppose part (1) of Stacks 08GW holds.  Then an object `E` of `D(𝒪_X)` supported on `T` is
isomorphic to `Rj_{V,*}(E|_V)` by a map `E ⟶ R_V E`.

This is the source's argument.  Stacks 08GW part (2) puts `E` in a distinguished triangle

`E ⟶ Rj_{U,*}E|_U ⊕ Rj_{V,*}E|_V ⟶ Rj_{P,*}E|_P ⟶ E[1]`;

support on `T` makes `E|_U` and `E|_P` vanish, hence also the two derived direct images, so the
third term of the triangle vanishes — whence the first map is an isomorphism — and the
`U`-summand of the second term vanishes, so the projection to the `V`-summand is an
isomorphism.  The composite of the two is a map `E ⟶ R_V E`. -/
theorem exists_isIso_derivedRestrictPush_of_cohomologySupportedOn
    (RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (αU : (edsRestrictPushOpen B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (edsRestrictPushEtale B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (edsRestrictPushInter B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (ηU : 𝟭 (Modules.{u, u} B S hS W.1 W.2) ⟶ edsRestrictPushOpen B S hS hsq)
    (ηV : 𝟭 (Modules.{u, u} B S hS W.1 W.2) ⟶ edsRestrictPushEtale B S hS hsq)
    (dU : edsRestrictPushOpen B S hS hsq ⟶ edsRestrictPushInter B S hS hsq)
    (dV : edsRestrictPushEtale B S hS hsq ⟶ edsRestrictPushInter B S hS hsq)
    (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
      biprod.desc (dU.app M) (-(dV.app M)) = 0)
    (hMV : ∀ M, (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) E)
    (hvan : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) E →
      ∀ {Y : AlgebraicSpaces B S hS} (g : Y ⟶ W) (hg : IsEtale B S hS g.hom),
        Set.range (pointsMap B S hS Y.1 g.hom) ⊆
            Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) →
          IsZero ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E))
    (hRUzero : IsZero ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E) → IsZero (RU.obj E))
    (hRPzero : IsZero ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E) → IsZero (RP.obj E)) :
    ∃ f : E ⟶ RV.obj E, IsIso f := by
  obtain ⟨fU, fV', gU, gV, δ, hδ⟩ :=
    exists_mem_distTriang_edsDerivedRestrictPushMayerVietoris B S hS hsq RU RV RP αU αV αP
      hRU hRV hRP ηU ηV dU dV hzero hMV E
  refine ⟨fV', ?_⟩
  have hU : IsZero (RU.obj E) :=
    hRUzero (hvan hE (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
      (range_pointsMap_edsOpenHom B S hS hsq).subset)
  have hP : IsZero (RP.obj E) :=
    hRPzero (hvan hE (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)
      (range_pointsMap_edsInterHom_subset B S hS hsq))
  have hlift : IsIso (biprod.lift fU fV') := (Triangle.isZero₃_iff_isIso₁ _ hδ).1 hP
  have hsnd := isIso_biprod_snd_of_isZero_fst (RU.obj E) (RV.obj E) hU
  rw [← biprod.lift_snd fU fV']
  infer_instance

end Pushforward

section SupportedComparison

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
    (edsEtale B S hS hsq).2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
    (edsEtale B S hS hsq).2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {shriekD RpushD : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2) ⥤ DerivedCategory (Modules.{u, u} B S hS W.1 W.2)}
  (adjShriek : shriekD ⊣ (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory)
  (adjPush : (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory ⊣ RpushD)

/-- The set `j^{-1}T` of points of the étale algebraic space of an elementary distinguished
square lying over `T = |X| \ |U|`. -/
def edsEtalePreimageComplementPoints :
    Set (points B S hS (edsEtale B S hS hsq).1) :=
  pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹'
    edsComplementPoints B S hS Uo

/-- The comparison `j_!F ⟶ Rj_*F` of clause (2)(c) of Stacks 08GG, available at an object `F`
of `D(𝒪_V)` at which the unit `F ⟶ (j_!F)|_V` of clause (2)(a) is invertible: it is the
adjunct, under the adjunction `(-)|_V ⊣ Rj_*`, of the inverse of that unit.

The source asserts the comparison only for `F` supported on `j^{-1}T`, and indeed its
construction needs clause (2)(a); a normalized comparison on all of `D(𝒪_V)` need not exist
for a nonseparated étale `j`. -/
def supportedShriekToPushforward
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2)) (h : IsIso (adjShriek.unit.app F)) :
    shriekD.obj F ⟶ RpushD.obj F :=
  letI := h
  adjPush.homEquiv (shriekD.obj F) F (inv (adjShriek.unit.app F))

/-- **The deduction of clause (2)(c) of Stacks 08GG from the other clauses.**  Let
`(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a scheme
`S`, set `T = |X| \ |U|` and let `F` be an object of `D(𝒪_V)` supported on `j^{-1}T`.  Granted
that the unit `F ⟶ (j_!F)|_V` of clause (2)(a) and the counit `(Rj_*F)|_V ⟶ F` of clause
(2)(b) are isomorphisms, and that clause (1)(a) holds at the two objects `j_!F` and `Rj_*F` of
`D(𝒪_X)`, the comparison `j_!F ⟶ Rj_*F` is an isomorphism.

The deduction is `CategoryTheory.Adjunction.isIso_homEquiv_inv_unit`: clauses (2)(a) and
(2)(b) make the restriction of the comparison invertible, and clause (1)(a) at its source and
at its target then makes the comparison itself invertible, by naturality of the unit of
`(-)|_V ⊣ Rj_*`.  The source instead obtains all three clauses at once from the base change of
the square to `V`.  All four inputs are theorems of the library; the unconditional clause (2)(c)
is `AlgebraicGeometry.Space.isIso_supportedShriekToPushforward_of_supported`. -/
theorem isIso_supportedShriekToPushforward
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2))
    (h2a : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
        (edsEtalePreimageComplementPoints B S hS hsq) F →
      IsIso (adjShriek.unit.app F))
    (h2b : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
        (edsEtalePreimageComplementPoints B S hS hsq) F →
      IsIso (adjPush.counit.app F))
    (h1aShriek : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2 (edsEtalePreimageComplementPoints B S hS hsq) F →
      IsIso (adjPush.unit.app (shriekD.obj F)))
    (h1aPush : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2 (edsEtalePreimageComplementPoints B S hS hsq) F →
      IsIso (adjPush.unit.app (RpushD.obj F)))
    (hF : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) F) :
    IsIso (supportedShriekToPushforward B S hS hsq adjShriek adjPush F (h2a hF)) := by
  have := h2a hF
  have := h2b hF
  have := h1aShriek hF
  have := h1aPush hF
  exact Adjunction.isIso_homEquiv_inv_unit adjShriek adjPush F

end SupportedComparison

end AlgebraicGeometry.Space

end
