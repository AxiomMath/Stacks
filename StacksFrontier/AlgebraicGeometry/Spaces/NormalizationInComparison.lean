module

public import Mathlib.AlgebraicGeometry.Normalization
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompCocontinuous

/-!
# Comparisons for the normalization of an algebraic space in another

Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` and let `Y ⟶ X' ⟶ X` be the
normalization of `X` in `Y`.  Stacks 0ABP asserts two comparisons.

1.  For an étale morphism `g : W ⟶ X`, the fibre product `W ×_X X'` is the normalization of `W`
    in `W ×_X Y`.
2.  If `X` and `Y` are representable, then `X'` is representable, and it is the normalization of
    the scheme `X` in the scheme `Y` of Morphisms, Section 035E.

## Main definitions

* `AlgebraicGeometry.Space.etaleAlgebraRestriction` is the restriction of algebra sheaves along
  the postcomposition functor of an étale morphism, i.e. the inverse image of algebras along an
  étale morphism of algebraic spaces.
* `AlgebraicGeometry.Space.AlgebraSheaf.integralClosureFunctor` makes the integral closure of
  the structure sheaf in an algebra a functor in the algebra.

## Main results

* `AlgebraicGeometry.Space.etaleAlgebraRestrictionIntegralClosureIso` is **part (1) of Stacks
  0ABP** at the level of algebras: the integral closure of the structure sheaf in an algebra is
  étale-local, so the algebra whose relative spectrum is the normalization restricts to the
  corresponding algebra on an étale `W`.  This is the whole of the source's reason for part (1),
  that the construction "commutes with étale base change", and it is unconditional.
* `AlgebraicGeometry.Space.normalizationInBaseChangeIso` is the geometric form of part (1):
  `W ×_X X'` is the normalization of `W` in `W ×_X Y`.
* `AlgebraicGeometry.Space.normalizationInIsoOfPushforwardAlgebraIso`: an algebraic space affine
  over `X` whose direct-image algebra is the integral closure of `𝒪_X` in `f_* 𝒪_Y` *is* the
  normalization of `X` in `Y`.  This is the uniqueness that part (2) turns into a comparison.
* `AlgebraicGeometry.Space.isRepresentable_normalizationIn` and
  `AlgebraicGeometry.Space.normalizationInRepresentableIso` are **part (2) of Stacks 0ABP**: in
  the representable case `X'` is representable and is identified, over `X`, with the given
  scheme-level normalization.

## Implementation notes

**The sieve comparison.**  The integral closure of `AlgebraicGeometry.Space.AlgebraSheaf` is the
sheafification of the subpresheaf of integral sections, so its sections over a chart are the
sections that are integral on the members of *some* étale covering of the chart.  Étale
restriction leaves the sections, the structure-algebra maps and the restriction maps unchanged,
so the integral sections agree on the nose; what has to be compared is the two covering
conditions, over the small étale site of `W` and over that of `X`.  They agree because
postcomposition along an étale morphism is both cover preserving (Stacks 03LP, continuity) and
cover lifting (Stacks 03LP, cocontinuity) — Stacks' remark that a covering of `jU` in `X_étale`
is the same thing as a covering of `U` in `W_étale`.  That is
`AlgebraicGeometry.Space.mem_topology_functorPullback_iff`, and it is the only geometric input to
part (1).

**What part (1) carries, and why.**  The geometric form compares
`AlgebraicGeometry.Space.relativeSpec` of the two algebras, which is the base-change clause of
Stacks 081V and is available as `AlgebraicGeometry.Space.BaseChangeCompatibility.baseChangeIso`.
Two further identifications are carried as named hypotheses, neither of them part (1):

* `halg` says that for an étale `g` the algebra pullback of Stacks 081V is étale restriction.
  Algebra pullback is extension of scalars along `g⁻¹ 𝒪_X ⟶ 𝒪_W`
  (`AlgebraicGeometry.Space.BaseChangeCompatibility.algebraPullback_isPushout`), which for an
  étale `g` is an isomorphism, so the pushout is the inverse image; but
  `AlgebraicGeometry.RingedToposHom.fSharpInverseImage` is nowhere shown to be an isomorphism
  for an étale morphism, and the inverse image of sheaves of *commutative rings* on the small
  étale site is nowhere identified with restriction along
  `AlgebraicGeometry.Space.smallEtalePostcomp`.  The module
  `StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange` does both for
  *modules*, as `AlgebraicGeometry.Space.etaleModulePullback_eq_restrictionModules`.
* `hbc` is Stacks 03LX for the structure sheaf, read as algebras: the direct image of `𝒪_Y`
  restricts to the direct image of `𝒪_{W ×_X Y}`.  Stacks 03LX for modules is
  `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIsoOfStructureSharp`, itself
  conditional on a compatibility `hsharp` of the structure maps of Stacks 03G8 that
  `StacksFrontier/AlgebraicGeometry/Spaces/StructureMapSharp.lean` does not prove; and the algebra
  form is in any case not stated anywhere.

**What part (2) carries, and why.**  `AlgebraicGeometry.Space.relativeSpec` is read off an
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence`, which has no inhabitant in this library,
so nothing about the *underlying functor* of `X'` can be computed: representability has to come
from exhibiting an algebraic space affine over `X` which is representable and whose direct-image
algebra is `𝒪'`.  Exhibiting it is the source's computation `ν^{-1}(U) = \Spec` of the integral
closure of `𝒪_X(U)` in `𝒪_Y(f^{-1}U)`.

That computation is **not** Descent, Proposition 03DX(2).  Proposition 03DX(2) for the small
étale site of an algebraic space is proved in
this library, unconditionally, by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`, both of which
carry `@[stacks 03DX]`; what it says is that a quasi-coherent module is cartesian between two
affine charts, which is a statement about the restriction maps of one sheaf and not a
computation of the sections of another.  Four separate inputs stand between it and `hcmp`, and
none of them is available:

* the sections clause of Stacks 0820 over an affine chart, that a locally integral section is
  integral there.  This is `AlgebraicGeometry.Space.AlgebraSheaf.IsIntegralLocalOnAffineCharts`,
  carried as a hypothesis; as the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureSheaf` record, discharging it needs
  exactly `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` together with flat descent of
  integrality along a finite affine refinement — so this is the one input for which 03DX(2) is
  the missing half, and that half is now present;
* quasi-coherence of the integral closure, the other assertion of Stacks 0820, which needs
  Stacks 035F and Stacks 081K, neither stated in this library;
* a computation of the sections of `AlgebraicGeometry.Space.pushforwardAlgebra` over an affine
  chart `U` as the global functions of `X ×_Y U`, which is what makes `𝒪_Y(f^{-1}U)` of the
  source's formula mean anything.  The library describes those sections only as a limit, by
  `AlgebraicGeometry.Space.directImageSectionsEquiv`;
* the object `Z` itself, an algebraic space affine over `X` representing the scheme
  normalization, which for a non-representable `X` has to be glued from charts.

So part (2) is stated against a given
`Z : AlgebraicGeometry.Space.AffineOver B S hS X`, representable and carrying the comparison
`hcmp` of its direct-image algebra with `𝒪'`, and what is proved is that `X'` is then that
object: representable, and identified with it over `X`.  The hypotheses `_eX`, `_eY`, `_hf₀` and
`_hN` are the source's own: they say that `X` and `Y` are representable, that `f₀` is the induced
morphism of schemes, and that the representing object `N₀` of `Z` is the normalization of the
scheme `X` in the scheme `Y`.  They are kept, in the shape the tag states them, and discarded by
the proof, which runs entirely through `hcmp`.

## References

* [Stacks Project, Tag 0ABP](https://stacks.math.columbia.edu/tag/0ABP)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Functoriality of the integral closure -/

namespace AlgebraSheaf

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- A morphism of algebra sheaves carries locally integral sections to locally integral
sections: on each member of a covering witnessing local integrality of a section, its image
satisfies the image of the monic equation. -/
theorem map_mem_locallyIntegralSections {A C : AlgebraSheaf.{u, m} B S hS F hF} (φ : A ⟶ C)
    (U : (SmallEtale B S hS F)ᵒᵖ) {a : A.right.obj.obj U}
    (ha : a ∈ A.locallyIntegralSections U) :
    (φ.right.hom.app U).hom a ∈ C.locallyIntegralSections U := by
  refine mem_locallyIntegralSections.2 ((SmallEtale.topology B S hS F).superset_covering ?_
    (mem_locallyIntegralSections.1 ha))
  intro V i hi
  rw [sieveOfSection_integralSubfunctor_apply]
  have hnat : (C.right.obj.map i.op).hom ((φ.right.hom.app U).hom a) =
      (φ.right.hom.app (op V)).hom ((A.right.obj.map i.op).hom a) :=
    (ConcreteCategory.congr_hom (φ.right.hom.naturality i.op) a).symm
  rw [hnat]
  refine mem_integralSections.2 (isIntegralElem_map (RingHom.id _)
    ((φ.right.hom.app (op V)).hom) ?_
    (mem_integralSections.1 ((sieveOfSection_integralSubfunctor_apply A a i).1 hi)))
  exact RingHom.ext fun r => φ.comm (op V) r

/-- The morphism of integral closures induced by a morphism of algebra sheaves. -/
def integralClosureMap {A C : AlgebraSheaf.{u, m} B S hS F hF} (φ : A ⟶ C) :
    integralClosureSheaf A ⟶ integralClosureSheaf C where
  right :=
    { hom :=
        { app := fun U => CommRingCat.ofHom
            (((φ.right.hom.app U).hom.comp (A.locallyIntegralSections U).subtype).codRestrict
              (C.locallyIntegralSections U)
              fun a => map_mem_locallyIntegralSections φ U a.2)
          naturality := fun U V i => by
            ext a
            exact Subtype.ext (ConcreteCategory.congr_hom (φ.right.hom.naturality i) a.1) } }
  comm U r := Subtype.ext (φ.comm U r)

/-- The integral closure of the structure sheaf in an algebra, as a functor of the algebra. -/
def integralClosureFunctor :
    AlgebraSheaf.{u, m} B S hS F hF ⥤ AlgebraSheaf.{u, m} B S hS F hF where
  obj A := integralClosureSheaf A
  map φ := integralClosureMap φ
  map_id _ := by
    refine Hom.ext (Sheaf.hom_ext ?_)
    ext U a
    rfl
  map_comp _ _ := by
    refine Hom.ext (Sheaf.hom_ext ?_)
    ext U a
    rfl

end AlgebraSheaf

/-! ### Étale restriction of algebra sheaves -/

variable {W X : AlgebraicSpaces B S hS}

/-- Restriction of sheaves of commutative rings along the postcomposition functor of an étale
morphism `g : W ⟶ X`: the inverse image of sheaves of rings along `g`, whose sections over a
chart of `W` are the sections over the same chart read as a chart of `X`. -/
abbrev etaleRingSheafRestriction (g : W ⟶ X) (hg : IsEtale B S hS g.hom) :
    Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{m} ⥤
      Sheaf (SmallEtale.topology B S hS W.1) CommRingCat.{m} :=
  (smallEtalePostcomp B S hS g hg).sheafPushforwardContinuous CommRingCat.{m}
    (SmallEtale.topology B S hS W.1) (SmallEtale.topology B S hS X.1)

/-- Restriction of algebra sheaves along an étale morphism `g : W ⟶ X`.  The sections, the
structure-algebra maps and the restriction maps are those of the original algebra, read on the
charts of `W` regarded as charts of `X`. -/
def etaleAlgebraRestriction (g : W ⟶ X) (hg : IsEtale B S hS g.hom) :
    AlgebraSheaf.{u, m} B S hS X.1 X.2 ⥤ AlgebraSheaf.{u, m} B S hS W.1 W.2 where
  obj A :=
    { right := (etaleRingSheafRestriction B S hS g hg).obj A.right
      algebraMap U := A.algebraMap ((smallEtalePostcomp B S hS g hg).op.obj U)
      algebraMap_natural i r :=
        A.algebraMap_natural ((smallEtalePostcomp B S hS g hg).op.map i) r }
  map φ :=
    { right := (etaleRingSheafRestriction B S hS g hg).map φ.right
      comm U r := φ.comm ((smallEtalePostcomp B S hS g hg).op.obj U) r }
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ### The integral closure is étale-local -/

/-- A sieve on an étale chart of `X` of the form `jU`, for `j` the postcomposition functor of an
étale `g : W ⟶ X`, is covering exactly when its pullback to the chart `U` of `W` is covering.

This is Stacks' remark that a covering of `jU` in the small étale site of `X` is the same thing
as a covering of `U` in that of `W`: one direction is cover preservation and the other is cover
lifting, i.e. the continuity and the cocontinuity of `j` in Stacks 03LP. -/
theorem mem_topology_functorPullback_iff (g : W ⟶ X) (hg : IsEtale B S hS g.hom)
    (U : SmallEtale B S hS W.1) (T : Sieve ((smallEtalePostcomp B S hS g hg).obj U)) :
    T.functorPullback (smallEtalePostcomp B S hS g hg) ∈ SmallEtale.topology B S hS W.1 U ↔
      T ∈ SmallEtale.topology B S hS X.1 ((smallEtalePostcomp B S hS g hg).obj U) := by
  refine ⟨fun h => ?_, SmallEtale.smallEtalePostcomp_cover_lift B S hS g hg U T⟩
  exact (SmallEtale.topology B S hS X.1).superset_covering
    (Sieve.functorPullback_pushforward_le _ T)
    ((SmallEtale.coverPreserving_smallEtalePostcomp B S hS g hg).cover_preserve h)

/-- The sieve witnessing local integrality of a section of an étale restriction is the pullback
of the sieve witnessing local integrality of the same section of the original algebra. -/
theorem sieveOfSection_integralSubfunctor_etaleAlgebraRestriction (g : W ⟶ X)
    (hg : IsEtale B S hS g.hom) (A : AlgebraSheaf.{u, m} B S hS X.1 X.2)
    {U : (SmallEtale B S hS W.1)ᵒᵖ}
    (a : A.right.obj.obj ((smallEtalePostcomp B S hS g hg).op.obj U)) :
    ((etaleAlgebraRestriction B S hS g hg).obj A).integralSubfunctor.sieveOfSection a =
      (A.integralSubfunctor.sieveOfSection a).functorPullback
        (smallEtalePostcomp B S hS g hg) :=
  rfl

/-- The locally integral sections of an étale restriction over a chart of `W` are the locally
integral sections of the original algebra over the same chart read as a chart of `X`. -/
theorem locallyIntegralSections_etaleAlgebraRestriction (g : W ⟶ X)
    (hg : IsEtale B S hS g.hom) (A : AlgebraSheaf.{u, m} B S hS X.1 X.2)
    (U : (SmallEtale B S hS W.1)ᵒᵖ) :
    ((etaleAlgebraRestriction B S hS g hg).obj A).locallyIntegralSections U =
      A.locallyIntegralSections ((smallEtalePostcomp B S hS g hg).op.obj U) := by
  refine SetLike.ext fun a => ?_
  exact mem_topology_functorPullback_iff B S hS g hg (unop U)
    (A.integralSubfunctor.sieveOfSection a)

/-- **Stacks 0ABP, part (1), at the level of algebras.**  The integral closure of the structure
sheaf in an algebra commutes with restriction along an étale morphism `g : W ⟶ X`.

This is the whole of the source's reason for part (1): the normalization of `X` in `Y` is the
relative spectrum of the integral closure of `𝒪_X` in `f_* 𝒪_Y`, and that construction is
étale-local, hence "commutes with étale base change". -/
@[stacks 0ABP "part (1), étale base change: the integral closure of the structure sheaf in an
  algebra is unchanged by restriction along an étale morphism, which is the construction of the
  normalization commuting with étale base change. The geometric form, for the relative spectra,
  is `normalizationInBaseChangeIso`."]
def etaleAlgebraRestrictionIntegralClosureIso (g : W ⟶ X) (hg : IsEtale B S hS g.hom)
    (A : AlgebraSheaf.{u, m} B S hS X.1 X.2) :
    (etaleAlgebraRestriction B S hS g hg).obj (AlgebraSheaf.integralClosureSheaf A) ≅
      AlgebraSheaf.integralClosureSheaf ((etaleAlgebraRestriction B S hS g hg).obj A) where
  hom :=
    { right :=
        { hom :=
            { app := fun U => CommRingCat.ofHom (Subring.inclusion
                (le_of_eq (locallyIntegralSections_etaleAlgebraRestriction
                  B S hS g hg A U).symm))
              naturality := fun _ _ _ => rfl } }
      comm _ _ := rfl }
  inv :=
    { right :=
        { hom :=
            { app := fun U => CommRingCat.ofHom (Subring.inclusion
                (le_of_eq (locallyIntegralSections_etaleAlgebraRestriction B S hS g hg A U)))
              naturality := fun _ _ _ => rfl } }
      comm _ _ := rfl }
  hom_inv_id := by
    refine AlgebraSheaf.Hom.ext (Sheaf.hom_ext ?_)
    ext U a
    rfl
  inv_hom_id := by
    refine AlgebraSheaf.Hom.ext (Sheaf.hom_ext ?_)
    ext U a
    rfl

/-! ### The normalization is determined by its direct-image algebra -/

variable (E : AffineAlgebraAntiEquivalence B S hS)

/-- An algebraic space affine over `X` whose direct image of the structure sheaf is the integral
closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y` is the normalization of `X` in `Y`, canonically and over
`X`: the anti-equivalence of Stacks 081V takes the two to isomorphic algebras. -/
def normalizationInIsoOfPushforwardAlgebraIso {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent)
    (Z : AffineOver B S hS X)
    (e : pushforwardAlgebra B S hS Z.obj ≅
      AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f))) :
    normalizationIn B S hS E f hqc' ≅ Z :=
  Iso.unop
    ((E.equivalence X).unitIso.app (op Z) ≪≫
      (E.equivalence X).inverse.mapIso
        ((E.pushforwardIso X).app (op Z) ≪≫
          ObjectProperty.isoMk
            (P := (AlgebraSheaf.IsQuasicoherent :
              ObjectProperty (AlgebraSheaf.{u, u} B S hS X.1 X.2)))
            (E.pushforward_obj X Z ≪≫ e)))

/-- The identification of the normalization of `X` in `Y` with such an algebraic space is over
`X`: composing it with the structure morphism of the latter gives the normalization morphism
`ν : X' ⟶ X`. -/
theorem normalizationInIsoOfPushforwardAlgebraIso_w {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent)
    (Z : AffineOver B S hS X)
    (e : pushforwardAlgebra B S hS Z.obj ≅
      AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f))) :
    (normalizationInIsoOfPushforwardAlgebraIso B S hS E f hqc' Z e).hom.hom.left ≫
        Z.obj.hom = (normalizationIn B S hS E f hqc').obj.hom :=
  Over.w _

/-! ### Part (1): étale base change -/

variable (C : BaseChangeCompatibility B S hS E)

/-- The algebra whose relative spectrum is the normalization of `X` in `Y`, pulled back along an
étale `g : W ⟶ X`, is the algebra whose relative spectrum is the normalization of `W` in
`W ×_X Y`: étale restriction commutes with the integral closure, and the direct image of the
structure sheaf base-changes. -/
def normalizationInAlgebraEtaleRestrictionIso {Y YW : AlgebraicSpaces B S hS}
    (g : W ⟶ X) (hg : IsEtale B S hS g.hom) (f : Y ⟶ X) (fW : YW ⟶ W)
    (halg : C.algebraPullback g ≅ etaleAlgebraRestriction.{u, u} B S hS g hg)
    (hbc : (etaleAlgebraRestriction.{u, u} B S hS g hg).obj
        (pushforwardAlgebra B S hS (Over.mk f)) ≅
      pushforwardAlgebra B S hS (Over.mk fW)) :
    (C.algebraPullback g).obj
        (AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f))) ≅
      AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk fW)) :=
  halg.app (AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f))) ≪≫
    etaleAlgebraRestrictionIntegralClosureIso.{u, u} B S hS g hg
      (pushforwardAlgebra B S hS (Over.mk f)) ≪≫
    AlgebraSheaf.integralClosureFunctor.mapIso hbc

/-- **Stacks 0ABP, part (1).**  For an étale morphism `g : W ⟶ X` the fibre product
`W ×_X X'` is the normalization of `W` in `W ×_X Y`.

The identification of the two algebras is étale-locality of the integral closure,
`etaleAlgebraRestrictionIntegralClosureIso`, together with `halg` and `hbc`; the identification
of the two relative spectra is the base-change clause of Stacks 081V. -/
@[stacks 0ABP "part (1), étale base change, in its geometric form. `halg` is the identification
  of the algebra pullback of Stacks 081V along an étale morphism with étale restriction and `hbc`
  is Stacks 03LX for the direct image of the structure sheaf, read as algebras; neither is part
  (1), and the module docstring records why each is carried. The content of part (1) is
  `etaleAlgebraRestrictionIntegralClosureIso`, which is unconditional."]
def normalizationInBaseChangeIso {Y YW : AlgebraicSpaces B S hS}
    (g : W ⟶ X) (hg : IsEtale B S hS g.hom) (f : Y ⟶ X) (p : YW ⟶ Y) (fW : YW ⟶ W)
    (_sq : IsPullback p fW f g)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent)
    (hqcW' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk fW))).IsQuasicoherent)
    (halg : C.algebraPullback g ≅ etaleAlgebraRestriction.{u, u} B S hS g hg)
    (hbc : (etaleAlgebraRestriction.{u, u} B S hS g hg).obj
        (pushforwardAlgebra B S hS (Over.mk f)) ≅
      pushforwardAlgebra B S hS (Over.mk fW)) :
    (C.affineBaseChange g).obj (normalizationIn B S hS E f hqc') ≅
      normalizationIn B S hS E fW hqcW' :=
  Iso.unop
    ((E.equivalence W).unitIso.app
          (op ((C.affineBaseChange g).obj (normalizationIn B S hS E f hqc'))) ≪≫
      (E.equivalence W).inverse.mapIso
        ((relativeSpecBaseChangeIso B S hS E C g (normalizationInAlgebra B S hS f hqc')).symm ≪≫
          (ObjectProperty.isoMk
            (P := (AlgebraSheaf.IsQuasicoherent :
              ObjectProperty (AlgebraSheaf.{u, u} B S hS W.1 W.2)))
            (normalizationInAlgebraEtaleRestrictionIso B S hS E C g hg f fW halg hbc) :
              (qcAlgebraPullback B S hS E C g).obj (normalizationInAlgebra B S hS f hqc') ≅
                normalizationInAlgebra B S hS fW hqcW'))).symm

/-! ### Part (2): the representable case -/

/-- The presheaf underlying an algebraic space affine over `X`, functorially. -/
def affineOverPresheaf (X : AlgebraicSpaces B S hS) :
    AffineOver B S hS X ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  obj Z := Z.obj.left.1
  map φ := φ.hom.left.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Stacks 0ABP, part (2).**  Let `X` and `Y` be representable, by `X₀` and `Y₀`, and let
`N₀` represent the normalization of the scheme `X₀` in the scheme `Y₀` of Stacks 035E.  Then the
normalization `X'` of `X` in `Y` is representable by `N₀`. -/
@[stacks 0ABP "part (2), comparison with the normalization of schemes. `Z` is the scheme
  normalization `AlgebraicGeometry.Scheme.Hom.normalization` of Stacks 035E, read inside the site
  as an algebraic space affine over `X`, and `hcmp` identifies its direct image of the structure
  sheaf with the integral closure of `𝒪_X` in `f_* 𝒪_Y`. That identification is the source's
  computation of `ν⁻¹(U)`. It is *not* Descent, Proposition 03DX(2): that proposition for the
  small étale site of an algebraic space is available here, unconditionally, as
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`, and it compares
  the sections over two affine charts rather than computing the sections of the integral closure.
  The module docstring lists what `hcmp` still needs."]
def normalizationInRepresentableIso {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent)
    {X₀ Y₀ N₀ : BigFppfOver B S hS} (_eX : X.1 ≅ yoneda.obj X₀) (_eY : Y.1 ≅ yoneda.obj Y₀)
    (f₀ : Y₀ ⟶ X₀) (_hf₀ : yoneda.map f₀ = _eY.inv ≫ f.hom ≫ _eX.hom)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map f₀)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map f₀)]
    (_hN : (BigFppfOver.toScheme B S hS).obj N₀ ≅
      ((BigFppfOver.toScheme B S hS).map f₀).normalization)
    (Z : AffineOver B S hS X) (eZ : Z.obj.left.1 ≅ yoneda.obj N₀)
    (hcmp : pushforwardAlgebra B S hS Z.obj ≅
      AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f))) :
    (normalizationIn B S hS E f hqc').obj.left.1 ≅ yoneda.obj N₀ :=
  (affineOverPresheaf B S hS X).mapIso
      (normalizationInIsoOfPushforwardAlgebraIso B S hS E f hqc' Z hcmp) ≪≫ eZ

/-- **Stacks 0ABP, part (2), representability.**  In the representable case the normalization
`X'` of `X` in `Y` is representable. -/
@[stacks 0ABP "part (2), representability of the normalization. The hypotheses are those of
  `normalizationInRepresentableIso`."]
theorem isRepresentable_normalizationIn {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent)
    {X₀ Y₀ N₀ : BigFppfOver B S hS} (eX : X.1 ≅ yoneda.obj X₀) (eY : Y.1 ≅ yoneda.obj Y₀)
    (f₀ : Y₀ ⟶ X₀) (hf₀ : yoneda.map f₀ = eY.inv ≫ f.hom ≫ eX.hom)
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map f₀)]
    [QuasiSeparated ((BigFppfOver.toScheme B S hS).map f₀)]
    (hN : (BigFppfOver.toScheme B S hS).obj N₀ ≅
      ((BigFppfOver.toScheme B S hS).map f₀).normalization)
    (Z : AffineOver B S hS X) (eZ : Z.obj.left.1 ≅ yoneda.obj N₀)
    (hcmp : pushforwardAlgebra B S hS Z.obj ≅
      AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f))) :
    (normalizationIn B S hS E f hqc').obj.left.1.IsRepresentable :=
  Functor.IsRepresentable.mk'
    (normalizationInRepresentableIso B S hS E f hqc' eX eY f₀ hf₀ hN Z eZ hcmp).symm

end AlgebraicGeometry.Space

end
