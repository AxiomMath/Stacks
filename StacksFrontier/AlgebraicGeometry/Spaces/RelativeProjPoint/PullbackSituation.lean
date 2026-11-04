module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Contains
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Shrink
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# Situation 0849 pulled back along a morphism of algebraic spaces

In Situation 0849 let `𝒜` be the quasi-coherent graded `𝒪_X`-algebra on the algebraic space `X`
over `S`, and let `g : X' ⟶ X` be a morphism of algebraic spaces over `S`.  Stacks 085C compares
the relative Proj of `𝒜` with the relative Proj of the pulled-back algebra `g^*𝒜` on `X'`.  This
file records that `g^*𝒜` is again the algebra of a Situation 0849, on `X'`.

The pulled-back algebra is the pullback of sheaves of graded algebras of Stacks 0FQX along the
morphism of small étale ringed topoi of Stacks 03G8 attached to `g`.  It is commutative and
concentrated in nonnegative degrees because `𝒜` is; its homogeneous pieces are the pullbacks of
modules of those of `𝒜`, which are quasi-coherent with no hypothesis on `g`
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`); and
their sections over every étale chart of `X'` are bounded by the cutoff of the site
(`AlgebraicGeometry.Space.hasCardinalLT_modulePullback_sections`).

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.pullbackAlgebra`: the graded `𝒪_{X'}`-algebra
  `g^*𝒜`.
* `AlgebraicGeometry.Space.RelativeProjSituation.pullback`: **Situation 0849 on `X'` with the
  algebra `g^*𝒜`.**

## Main results

* `AlgebraicGeometry.Space.hasCardinalLT_modulePullback_sections`: the sections of the pullback
  of a quasi-coherent module whose sections are bounded by the cutoff are bounded by the cutoff,
  over every étale chart.

## Implementation notes

The pullback of sheaves of graded algebras is available for algebras whose sections lie in the
universe `u` of the coefficient rings, while the homogeneous sections of `𝒜` lie in an arbitrary
universe `m`.  As for the restrictions `f^*𝒜` of Stacks 084B
(`AlgebraicGeometry.Space.RelativeProjSituation.pointAlgebra`), `g^*𝒜` is therefore the pullback
of the re-presentation `AlgebraicGeometry.Space.RelativeProjSituation.smallAlgebra` of `𝒜` with
sections in `u`, which is identified with `𝒜` degreewise and sectionwise, compatibly with
multiplication and unit (`AlgebraicGeometry.Space.RelativeProjSituation.smallAlgebraEquiv`), and
with `𝒜` itself as a sheaf of graded algebras when `m = u`
(`AlgebraicGeometry.Space.RelativeProjSituation.smallAlgebraIso`).

The size bound over an étale chart `U ⟶ X'` is read off the scheme point `U ⟶ X' ⟶ X`: pullback
along the étale morphism `U ⟶ X'` is étale restriction (Stacks 03LW), so the sections of `g^*ℳ`
over `U` are the global sections of the pullback of `ℳ` along the composite, which
`AlgebraicGeometry.Space.exists_mk_modulePullback_sections_le` bounds.

## References

* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An étale chart `U = (V, u)` of `X'` is the image of the identity chart of `V` under
postcomposition with `u`. -/
theorem smallEtalePostcomp_obj_idEtaleChart {X' : AlgebraicSpaces B S hS}
    (U : SmallEtale B S hS X'.1) :
    (smallEtalePostcomp B S hS (ObjectProperty.homMk U.1.hom : yonedaSpace B S hS U.1.left ⟶ X')
      (isEtale_of_presheaf_etale B S hS U.2)).obj (idEtaleChart B S hS U.1.left) = U := by
  obtain ⟨⟨V, ⟨⟨⟩⟩, u⟩, hu⟩ := U
  exact Stacks.CategoryTheory.fullSubcategory_eq_of_obj_eq
    (congrArg CostructuredArrow.mk (Category.id_comp u) :)

/-- **The sections of the pullback of a quasi-coherent module are bounded by the cutoff of the
site**, over every étale chart, as soon as those of the module are.  For an étale chart `(V, u)`
of `X'` the sections of `g^*ℳ` over it are the global sections of the pullback of `ℳ` along the
scheme point `u ≫ g` of `X`, by Stacks 03LW and the composition law of pullbacks, and those are
bounded by `AlgebraicGeometry.Space.exists_mk_modulePullback_sections_le`. -/
theorem hasCardinalLT_modulePullback_sections {X X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (hbound : ∀ U : (SmallEtale B S hS X.1)ᵒᵖ, HasCardinalLT (M.val.obj U) B.cutoff)
    (U : (SmallEtale B S hS X'.1)ᵒᵖ) :
    HasCardinalLT (((modulePullback B S hS g).obj M).val.obj U) B.cutoff := by
  let V := U.unop.1.left
  let a : yonedaSpace B S hS V ⟶ X' := ObjectProperty.homMk U.unop.1.hom
  have ha : IsEtale B S hS a.hom := isEtale_of_presheaf_etale B S hS U.unop.2
  obtain ⟨c, hc, hle⟩ := exists_mk_modulePullback_sections_le X M hM hbound V (U.unop.1.hom ≫ g.hom)
  let N := (modulePullback B S hS (pointHom (U.unop.1.hom ≫ g.hom))).obj M
  let G := (modulePullback B S hS g).obj M
  have hiso : ∀ {P Q : Modules.{u, u} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)}
      (e : P ≅ Q) (W : (SmallEtale B S hS (yoneda.obj V))ᵒᵖ),
      #(P.val.obj W) = #(Q.val.obj W) := fun e W =>
    Cardinal.mk_congr
      { toFun := fun x => e.hom.val.app W x
        invFun := fun y => e.inv.val.app W y
        left_inv := fun x => congrArg (fun k => k.val.app W x) e.hom_inv_id
        right_inv := fun y => congrArg (fun k => k.val.app W y) e.inv_hom_id }
  have e1 : #(G.val.obj U) =
      #(((etaleModulePullback B S hS a ha).obj G).val.obj (op (idEtaleChart B S hS V))) :=
    congrArg (fun W => #(G.val.obj (op W))) (smallEtalePostcomp_obj_idEtaleChart U.unop).symm
  have e2 : #(((etaleModulePullback B S hS a ha).obj G).val.obj (op (idEtaleChart B S hS V))) =
      #(N.val.obj (op (idEtaleChart B S hS V))) :=
    (hiso ((modulePullbackIsoEtaleModulePullback B S hS a ha).app G) _).symm.trans
      (hiso ((modulePullbackCompIso B S hS a g).app M) _)
  have e3 : #(N.val.obj (op (idEtaleChart B S hS V))) =
      #(N.val.obj (op ((selfOpensFunctor B S hS V).obj ⊤))) := by
    rw [selfOpensFunctor_obj]
    exact Cardinal.mk_congr ((N.val.presheaf.mapIso
      (openChartTopIso B S hS (yoneda.obj V) (idEtaleChart B S hS V)).op)
        |>.addCommGroupIsoToAddEquiv.toEquiv)
  rw [hasCardinalLT_iff_cardinal_mk_lt]
  exact lt_of_le_of_lt ((e1.trans (e2.trans e3)).le.trans (hle ⊤)) hc

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m}) {X' : AlgebraicSpaces s.site s.base s.containsBase}
  (g : X' ⟶ s.space)

/-- **The pulled-back graded algebra `g^*𝒜`** on `X'`: the pullback of sheaves of graded algebras
along the morphism of small étale ringed topoi of `g`, applied to the re-presentation of `𝒜` with
sections in the universe `u`. -/
abbrev pullbackAlgebra : SheafOfModules.GradedAlgebra.{u, u}
    (structureRingSheaf s.site s.base s.containsBase X') :=
  (gradedPull (X := smallEtaleRingedTopos s.site s.base s.containsBase X')
    (Y := smallEtaleRingedTopos s.site s.base s.containsBase s.space)
    (smallEtaleRingedToposHom s.site s.base s.containsBase g)).obj s.smallAlgebra

/-- **Situation 0849 pulled back along a morphism of algebraic spaces `g : X' ⟶ X`**: the same
site and base scheme, the algebraic space `X'`, and the quasi-coherent graded `𝒪_{X'}`-algebra
`g^*𝒜`.  Commutativity and the vanishing in negative degrees pass to the pullback; the pieces are
quasi-coherent for an arbitrary `g`; and their sections are bounded by the cutoff by
`AlgebraicGeometry.Space.hasCardinalLT_modulePullback_sections`. -/
def pullback : RelativeProjSituation.{u, u} where
  site := s.site
  base := s.base
  containsBase := s.containsBase
  space := X'
  algebra := s.pullbackAlgebra g
  mul_comm i j U a b :=
    (Stacks.Sheaves.GradedAlgebraPullback.isCommutative_toposPullbackGradedAlgebra
      (X := smallEtaleRingedTopos s.site s.base s.containsBase X')
      (Y := smallEtaleRingedTopos s.site s.base s.containsBase s.space)
      (smallEtaleRingedToposModulesHom s.site s.base s.containsBase g) s.smallAlgebra
      (hB := ⟨s.shrink.mul_comm⟩)).mul_comm i j U a b
  negative_isZero n hn :=
    haveI := (modulePullbackAdjunction s.site s.base s.containsBase g).isLeftAdjoint
    (modulePullback s.site s.base s.containsBase g).map_isZero (s.isZero_smallAlgebra_piece n hn)
  isQuasicoherent n :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite s.site s.base s.containsBase g _
      (s.isQuasicoherent_smallAlgebra n)
  sections_hasCardinalLT n U :=
    hasCardinalLT_modulePullback_sections g (s.smallAlgebra.piece n)
      (s.isQuasicoherent_smallAlgebra n) (s.shrink.sections_hasCardinalLT n) U

/-- The site of the pulled-back situation is the site of `s`. -/
@[simp] theorem pullback_site : (s.pullback g).site = s.site := rfl

/-- The base scheme of the pulled-back situation is the base scheme of `s`. -/
@[simp] theorem pullback_base : (s.pullback g).base = s.base := rfl

/-- The algebraic space of the pulled-back situation is `X'`. -/
@[simp] theorem pullback_space : (s.pullback g).space = X' := rfl

/-- The graded algebra of the pulled-back situation is `g^*𝒜`. -/
theorem pullback_algebra : (s.pullback g).algebra = s.pullbackAlgebra g := rfl

end RelativeProjSituation

end AlgebraicGeometry.Space

end
