module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistEventual
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.EventualBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjFunctoriality

/-!
# Functoriality of relative Proj for maps surjective or bijective in high degree

Let `S` be a scheme, `X` an algebraic space over `S` and `ψ : 𝒜 ⟶ ℬ` a map of quasi-coherent graded
`𝒪_X`-algebras. Writing `P = Proj_X(𝒜)` and `Q = Proj_X(ℬ)`, the map `ψ` induces a morphism
`r_ψ : U(ψ) ⟶ P` on an open subspace `U(ψ) ⊆ Q`. This file shows that if `ψ` is surjective, or
bijective, in all large degrees then `U(ψ) = Q`, and records what this gives for the induced
morphism and for the comparison maps on the twists.

The hypotheses are read over the scheme points of the base: for every `T`-point `f` of `X`, the
restricted map `ψ|_{T,f} : f^*𝒜 ⟶ f^*ℬ` of graded algebras on the scheme of `T` is an epimorphism,
or an isomorphism, in all sufficiently large degrees.

## Main results

* `AlgebraicGeometry.Space.isDefinedOn_of_eventually_epi`: when every restriction of `ψ` is an
  epimorphism in all large degrees, every point of `Q` lies in the domain of definition.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.relativeMapSubfunctor_eq_top_of_eventually_epi`:
  the same assertion as an equality of subfunctors, `U(ψ) = Q`.
* `AlgebraicGeometry.Space.isDefinedOn_of_eventually_isIso` and
  `AlgebraicGeometry.Space.RelativeProjHomPoints.relativeMapSubfunctor_eq_top_of_eventually_isIso`:
  the same assertions when every restriction of `ψ` is an isomorphism in all large degrees.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.isIso_relativeMapSpaceHom`: in that case
  `r_ψ : U(ψ) ⟶ P` is an isomorphism of algebraic spaces.
* `AlgebraicGeometry.Space.isClosedImmersion_pointRelativeMapHom_of_eventually_epi`: when every
  restriction of `ψ` is an epimorphism in all large degrees, over each scheme point of the base
  `r_{ψ|_{T,f}}` is a closed immersion of schemes.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.isIso_relativeTwistSpaceMap_of_eventually_isIso`:
  when every restriction of `ψ` is an isomorphism in all large degrees, the maps
  `θ : r_ψ^*𝒪_P(n) ⟶ 𝒪_Q(n)` are isomorphisms.
* `AlgebraicGeometry.Space.epi_pointTwistMap_of_eventually_epi`,
  `AlgebraicGeometry.Space.isIso_pointTwistMap_of_eventually_isIso` and
  `AlgebraicGeometry.Space.isIso_pointTwistMap_of_generatedInDegreeOne`: the comparison maps on the
  twists over the opens of each scheme point of the base are epimorphisms, or isomorphisms.

## References

* [Stacks Project, Tag 085H](https://stacks.math.columbia.edu/tag/085H)
* [Stacks Project, Tag 085I](https://stacks.math.columbia.edu/tag/085I)
* [Stacks Project, Tag 085J](https://stacks.math.columbia.edu/tag/085J)
* [Stacks Project, Tag 085F](https://stacks.math.columbia.edu/tag/085F)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 07ZI](https://stacks.math.columbia.edu/tag/07ZI)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
* [Stacks Project, Tag 07ZK](https://stacks.math.columbia.edu/tag/07ZK)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Filter TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X} {πQ : Q ⟶ X}

/-! ### Satisfiability of the hypotheses -/

/-- The identity homomorphism of a sheaf-level graded algebra: the identity of each homogeneous
piece. -/
def idSheafGradedAlgebraHom {Z : Scheme.{u}} (A : SheafGradedAlgebra Z) :
    SheafGradedAlgebraHom A A where
  app _ := 𝟙 _
  app_mul _ _ _ _ _ := rfl
  app_one _ := rfl

/-- For any presentation of a relative Proj, the family of identity maps of the restricted graded
algebras is an isomorphism in all sufficiently large degrees. -/
theorem eventually_isIso_app_idSheafGradedAlgebraHom
    (d : RelativeProjPoints B S hS πQ) (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    ∀ᶠ n : ℕ in atTop, IsIso ((idSheafGradedAlgebraHom (d.algebra T f)).app (n : ℤ)) :=
  Eventually.of_forall fun _ => inferInstanceAs (IsIso (𝟙 _))

/-! ### The domain of definition is everything -/

section Pointwise

variable {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
    {ψ : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      SheafGradedAlgebraHom (dP.algebra T f) (dQ.algebra T f)}

/-- If the domain of `ψ|_{T,f}` is everything, every point of `Q` lies in the domain of definition
of `ψ`. -/
private theorem isDefinedOn_of_relativeMapDomain_eq_top (T : BigFppfOver B S hS)
    (f : yoneda.obj T ⟶ X) (hdom : (ψ T f).relativeMapDomain = ⊤) {T' : BigFppfOver B S hS}
    (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q) (hu : u ≫ πQ = yoneda.map r ≫ f) :
    IsDefinedOn dP dQ ψ T f r u hu := by
  change dQ.sectionOfPoint T f r u hu ⁻¹ᵁ (ψ T f).relativeMapDomain = ⊤
  rw [hdom, Scheme.Hom.preimage_top]

/-- If every restriction of `ψ` is an epimorphism in all sufficiently large degrees then every
point of `Q = Proj_X(ℬ)` lies in the domain of definition of `ψ`. -/
@[stacks 085H "part (1): every point of Q lies in the domain of definition",
  stacks 085J "part (1): every point of Q lies in the domain of definition"]
theorem isDefinedOn_of_eventually_epi
    (hsurj : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      ∀ᶠ d : ℕ in atTop, Epi ((ψ T f).app (d : ℤ)))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) {T' : BigFppfOver B S hS}
    (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q) (hu : u ≫ πQ = yoneda.map r ≫ f) :
    IsDefinedOn dP dQ ψ T f r u hu :=
  isDefinedOn_of_relativeMapDomain_eq_top T f
    (relativeMapDomain_eq_top_of_eventually_epi (ψ T f) (hsurj T f)) r u hu

/-- If every restriction of `ψ` is an isomorphism in all sufficiently large degrees then every
point of `Q = Proj_X(ℬ)` lies in the domain of definition of `ψ`. -/
@[stacks 085I "part (1): every point of Q lies in the domain of definition"]
theorem isDefinedOn_of_eventually_isIso
    (hiso : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      ∀ᶠ d : ℕ in atTop, IsIso ((ψ T f).app (d : ℤ)))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) {T' : BigFppfOver B S hS}
    (r : T' ⟶ T) (u : yoneda.obj T' ⟶ Q) (hu : u ≫ πQ = yoneda.map r ≫ f) :
    IsDefinedOn dP dQ ψ T f r u hu :=
  isDefinedOn_of_relativeMapDomain_eq_top T f
    (relativeMapDomain_eq_top_of_eventually_isIso (ψ T f) (hiso T f)) r u hu

/-! ### The induced point of `P`, read through the scheme-level morphism -/

/-- The induced point of `P` determines the point of `Q` it comes from, as soon as the
scheme-level morphism `r_{ψ|_{T,f}}` of Stacks 07ZG is a monomorphism. -/
theorem injective_pointHomOn (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T)
    (hmono : Mono (relativeMapHom (ψ T f)))
    (u v : yoneda.obj T' ⟶ Q) (hu : u ≫ πQ = yoneda.map r ≫ f)
    (hv : v ≫ πQ = yoneda.map r ≫ f)
    (hdu : IsDefinedOn dP dQ ψ T f r u hu) (hdv : IsDefinedOn dP dQ ψ T f r v hv)
    (h : pointHomOn dP dQ ψ T f r u hu hdu = pointHomOn dP dQ ψ T f r v hv hdv) :
    u = v := by
  have key : dP.sectionOfPoint T f r (pointHomOn dP dQ ψ T f r u hu hdu)
        (pointHomOn_comp dP dQ ψ T f r u hu hdu) =
      dP.sectionOfPoint T f r (pointHomOn dP dQ ψ T f r v hv hdv)
        (pointHomOn_comp dP dQ ψ T f r v hv hdv) := by
    congr 1
  rw [sectionOfPoint_pointHomOn, sectionOfPoint_pointHomOn] at key
  refine dQ.eq_of_sectionOfPoint_eq T f r u v hu hv ?_
  rw [← liftToOpens_comp_ι (dQ.sectionOfPoint T f r u hu) _ hdu,
    ← liftToOpens_comp_ι (dQ.sectionOfPoint T f r v hv) _ hdv,
    (cancel_mono (relativeMapHom (ψ T f))).1 key]

/-- A morphism into an open subscheme is the factorization of its own composite with the
inclusion. -/
theorem liftToOpens_comp_ι_self {Y Z : Scheme.{u}} (D : Z.Opens) (t : Y ⟶ D.toScheme)
    (h : (t ≫ D.ι) ⁻¹ᵁ D = ⊤) : liftToOpens (t ≫ D.ι) D h = t :=
  (liftToOpens_unique _ _ h t rfl).symm

/-- Every section of the scheme-level relative Proj of `ℬ|_T` comes from a point of
`Q = Proj_X(ℬ)`. -/
theorem exists_sectionOfPoint_eq (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T)
    (g : (BigFppfOver.toScheme B S hS).obj T' ⟶ (relativeProj (dQ.algebra T f)).scheme)
    (hg : g ≫ (relativeProj (dQ.algebra T f)).toBase = (BigFppfOver.toScheme B S hS).map r) :
    ∃ (u : yoneda.obj T' ⟶ Q) (hu : u ≫ πQ = yoneda.map r ≫ f),
      dQ.sectionOfPoint T f r u hu = g :=
  ⟨((dQ.pointEquivProjOver T f r).symm ⟨g, hg⟩).1,
   ((dQ.pointEquivProjOver T f r).symm ⟨g, hg⟩).2,
   congrArg Subtype.val ((dQ.pointEquivProjOver T f r).apply_symm_apply ⟨g, hg⟩)⟩

/-- The induced point of `P` is identified by its section: if the section of `u` factors as `t`
through the open `U(ψ|_{T,f})` and the section of `w` is `t` followed by the scheme-level
morphism `r_{ψ|_{T,f}}`, then `u` induces `w`. -/
theorem pointHomOn_eq_of_sectionOfPoint_eq (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T)
    (t : (BigFppfOver.toScheme B S hS).obj T' ⟶ (ψ T f).relativeMapDomain.toScheme)
    (u : yoneda.obj T' ⟶ Q) (hu : u ≫ πQ = yoneda.map r ≫ f)
    (hd : IsDefinedOn dP dQ ψ T f r u hu)
    (hsec : dQ.sectionOfPoint T f r u hu = t ≫ (ψ T f).relativeMapDomain.ι)
    (w : yoneda.obj T' ⟶ P) (hw : w ≫ πP = yoneda.map r ≫ f)
    (hws : dP.sectionOfPoint T f r w hw = t ≫ relativeMapHom (ψ T f)) :
    pointHomOn dP dQ ψ T f r u hu hd = w := by
  have hd2 : (t ≫ (ψ T f).relativeMapDomain.ι) ⁻¹ᵁ (ψ T f).relativeMapDomain = ⊤ := by
    rw [← hsec]; exact hd
  refine dP.eq_of_sectionOfPoint_eq T f r _ w (pointHomOn_comp dP dQ ψ T f r u hu hd) hw ?_
  rw [sectionOfPoint_pointHomOn, hws,
    liftToOpens_congr (dQ.sectionOfPoint T f r u hu) _ hsec (ψ T f).relativeMapDomain hd hd2,
    liftToOpens_comp_ι_self]

/-- Every point of `P` is induced by one of `Q`, when the scheme-level morphism `r_{ψ|_{T,f}}` of
Stacks 07ZG is an isomorphism defined on all of `Proj_T(ℬ|_T)`. -/
theorem exists_pointHomOn_eq (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T)
    (hiso : IsIso (relativeMapHom (ψ T f)))
    (hdom : (ψ T f).relativeMapDomain = ⊤)
    (w : yoneda.obj T' ⟶ P) (hw : w ≫ πP = yoneda.map r ≫ f) :
    ∃ (u : yoneda.obj T' ⟶ Q) (hu : u ≫ πQ = yoneda.map r ≫ f)
      (hd : IsDefinedOn dP dQ ψ T f r u hu),
      pointHomOn dP dQ ψ T f r u hu hd = w := by
  have hs := dP.sectionOfPoint_comp_toBase T f r w hw
  have hg : ((dP.sectionOfPoint T f r w hw ≫ inv (relativeMapHom (ψ T f))) ≫
      (ψ T f).relativeMapDomain.ι) ≫ (relativeProj (dQ.algebra T f)).toBase =
      (BigFppfOver.toScheme B S hS).map r := by
    rw [Category.assoc, ← relativeMapHom_comp_toBase, Category.assoc,
      IsIso.inv_hom_id_assoc, hs]
  obtain ⟨u, hu, hsec⟩ := exists_sectionOfPoint_eq T f r _ hg
  have hd := isDefinedOn_of_relativeMapDomain_eq_top (dP := dP) T f hdom r u hu
  refine ⟨u, hu, hd, pointHomOn_eq_of_sectionOfPoint_eq T f r _ u hu hd hsec w hw ?_⟩
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end Pointwise

/-! ### The scheme-level assertions at a point of the base -/

section AtPoints

variable {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
    (ψ : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      SheafGradedAlgebraHom (dP.algebra T f) (dQ.algebra T f))

/-- If every restriction of `ψ` is an epimorphism in all sufficiently large degrees then over each
scheme point `(T, f)` of `X` the morphism `r_{ψ|_{T,f}} : Proj_T(ℬ|_T) ⟶ Proj_T(𝒜|_T)` of Stacks
07ZG is a closed immersion of schemes. -/
@[stacks 085H "part (2): a closed immersion over each scheme point of the base",
  stacks 085J "part (2): a closed immersion over each scheme point of the base"]
theorem isClosedImmersion_pointRelativeMapHom_of_eventually_epi
    (hsurj : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      ∀ᶠ d : ℕ in atTop, Epi ((ψ T f).app (d : ℤ)))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    _root_.AlgebraicGeometry.IsClosedImmersion (relativeMapHom (ψ T f)) :=
  isClosedImmersion_relativeMapHom_of_eventually_epi (ψ T f) (hsurj T f)

/-- If every restriction of `ψ` is an epimorphism in all sufficiently large degrees then, over
every affine open of every scheme point of the base, the comparison maps of Stacks 01MY on the
`n`-th twist are epimorphisms. -/
@[stacks 085H "part (3): the maps on twists are surjective, chart by chart"]
theorem epi_pointTwistMap_of_eventually_epi
    (hsurj : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      ∀ᶠ d : ℕ in atTop, Epi ((ψ T f).app (d : ℤ)))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {V : ((BigFppfOver.toScheme B S hS).obj T).Opens} (hV : IsAffineOpen V) (n : ℤ) :
    Epi ((Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData ((dP.algebra T f).grading V)
      ((dQ.algebra T f).grading V) ((ψ T f).sectionHom V)).twistMap n) :=
  epi_chart_twistMap_of_eventually_epi (ψ T f) (hsurj T f) hV n

/-- If every restriction of `ψ` is an isomorphism in all sufficiently large degrees then the
comparison maps of Stacks 01MY on the twists are isomorphisms, over every open of every scheme
point of the base. -/
theorem isIso_pointTwistMap_of_eventually_isIso
    (hiso : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      ∀ᶠ d : ℕ in atTop, IsIso ((ψ T f).app (d : ℤ)))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    (V : ((BigFppfOver.toScheme B S hS).obj T).Opens) (n : ℤ) :
    IsIso ((Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData ((dP.algebra T f).grading V)
      ((dQ.algebra T f).grading V) ((ψ T f).sectionHom V)).twistMap n) :=
  isIso_chart_twistMap_of_eventually_isIso (ψ T f) (hiso T f) V n

/-- If every restriction of `ψ` is an epimorphism in all sufficiently large degrees and `𝒜` is
generated in degree one over every affine open of every scheme point of the base, the comparison
maps of Stacks 01MY on the twists over those affine opens are isomorphisms. -/
@[stacks 085J "part (3): the maps on twists are isomorphisms, chart by chart"]
theorem isIso_pointTwistMap_of_generatedInDegreeOne
    (hsurj : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      ∀ᶠ d : ℕ in atTop, Epi ((ψ T f).app (d : ℤ)))
    (hgen : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
      (U : ((BigFppfOver.toScheme B S hS).obj T).Opens), IsAffineOpen U →
        (dP.algebra T f).IsGeneratedInDegreeOneAt U)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {V : ((BigFppfOver.toScheme B S hS).obj T).Opens} (hV : IsAffineOpen V) (n : ℤ) :
    IsIso ((Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData ((dP.algebra T f).grading V)
      ((dQ.algebra T f).grading V) ((ψ T f).sectionHom V)).twistMap n) :=
  isIso_chart_twistMap_of_generatedInDegreeOne (ψ T f) (hsurj T f) (hgen T f) hV n

end AtPoints

/-! ### The open subspace and the morphism of algebraic spaces -/

namespace RelativeProjHomPoints

variable {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
    (hψ : RelativeProjHomPoints dP dQ)

/-- If every restriction of `ψ` is an epimorphism in all sufficiently large degrees then the open
subspace `U(ψ)` of Stacks 085F is all of `Q = Proj_X(ℬ)`. -/
@[stacks 085H "part (1): U(ψ) = Q", stacks 085J "part (1): U(ψ) = Q"]
theorem relativeMapSubfunctor_eq_top_of_eventually_epi
    (hsurj : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      ∀ᶠ d : ℕ in atTop, Epi ((hψ.hom T f).app (d : ℤ))) :
    hψ.relativeMapSubfunctor = ⊤ :=
  top_le_iff.1 fun Y _ _ =>
    isDefinedOn_of_eventually_epi hsurj Y.unop _ (𝟙 Y.unop) _ _

/-- If every restriction of `ψ` is an isomorphism in all sufficiently large degrees then the open
subspace `U(ψ)` of Stacks 085F is all of `Q = Proj_X(ℬ)`. -/
@[stacks 085I "part (1): U(ψ) = Q"]
theorem relativeMapSubfunctor_eq_top_of_eventually_isIso
    (hiso : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      ∀ᶠ d : ℕ in atTop, IsIso ((hψ.hom T f).app (d : ℤ))) :
    hψ.relativeMapSubfunctor = ⊤ :=
  top_le_iff.1 fun Y _ _ =>
    isDefinedOn_of_eventually_isIso hiso Y.unop _ (𝟙 Y.unop) _ _

/-- The morphism `r_ψ` of Stacks 085F is bijective on the points of every object of the site, when
every restriction of `ψ` is an isomorphism in all sufficiently large degrees. -/
theorem bijective_app_relativeMapSpaceHom
    (hiso : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      ∀ᶠ d : ℕ in atTop, IsIso ((hψ.hom T f).app (d : ℤ)))
    (Y : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Bijective (hψ.relativeMapSpaceHom.app Y) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨x', hx'⟩ hxx
    obtain rfl : x = x' := by
      set u : yoneda.obj Y.unop ⟶ Q := yonedaEquiv.symm x with hudef
      set u' : yoneda.obj Y.unop ⟶ Q := yonedaEquiv.symm x' with hu'def
      have hx1 : IsDefined dP dQ hψ.hom Y.unop u := hx
      have hx1' : IsDefined dP dQ hψ.hom Y.unop u' := hx'
      have he : pointHomAt dP dQ hψ.hom Y.unop u hx1 =
          pointHomAt dP dQ hψ.hom Y.unop u' hx1' := yonedaEquiv.injective hxx
      have hbase : u' ≫ πQ = u ≫ πQ := by
        rw [← pointHomAt_comp dP dQ hψ.hom Y.unop u' hx1',
          ← pointHomAt_comp dP dQ hψ.hom Y.unop u hx1, he]
      have hu' : u' ≫ πQ = yoneda.map (𝟙 Y.unop) ≫ (u ≫ πQ) := by
        rw [hbase, CategoryTheory.Functor.map_id, Category.id_comp]
      have hdu' : IsDefinedOn dP dQ hψ.hom Y.unop (u ≫ πQ) (𝟙 Y.unop) u' hu' :=
        isDefinedOn_of_eventually_isIso hiso _ _ _ _ _
      have := isIso_relativeMapHom_of_eventually_isIso (hψ.hom Y.unop (u ≫ πQ)) (hiso _ _)
      have he2 : pointHomOn dP dQ hψ.hom Y.unop (u ≫ πQ) (𝟙 Y.unop) u (comp_eq_self u) hx1 =
          pointHomOn dP dQ hψ.hom Y.unop (u ≫ πQ) (𝟙 Y.unop) u' hu' hdu' :=
        he.trans (pointHomOn_congr_base dP dQ hψ.hom Y.unop (u' ≫ πQ) (u ≫ πQ) hbase
          (𝟙 Y.unop) u' (comp_eq_self u') hu' hx1' hdu')
      have heq := injective_pointHomOn Y.unop (u ≫ πQ) (𝟙 Y.unop) inferInstance u u'
        (comp_eq_self u) hu' hx1 hdu' he2
      rw [hudef, hu'def] at heq
      exact yonedaEquiv.symm.injective heq
    rfl
  · intro p
    obtain ⟨u, hu, hd, hp⟩ := exists_pointHomOn_eq (ψ := hψ.hom) Y.unop
      (yonedaEquiv.symm p ≫ πP) (𝟙 Y.unop)
      (isIso_relativeMapHom_of_eventually_isIso _ (hiso _ _))
      (relativeMapDomain_eq_top_of_eventually_isIso _ (hiso _ _))
      (yonedaEquiv.symm p) (comp_eq_self _)
    have hmem : yonedaEquiv u ∈ hψ.relativeMapSubfunctor.obj (op Y.unop) :=
      (hψ.mem_relativeMapSubfunctor_iff' Y.unop u).2
        (isDefinedOn_of_eventually_isIso hiso _ _ _ _ _)
    refine ⟨⟨yonedaEquiv u, hmem⟩, ?_⟩
    rw [hψ.app_relativeMapSpaceHom Y.unop (yonedaEquiv.symm p ≫ πP) (𝟙 Y.unop) u hu hd hmem,
      hp, Equiv.apply_symm_apply]

/-- If every restriction of `ψ` is an isomorphism in all sufficiently large degrees then
`r_ψ : U(ψ) ⟶ P` is an isomorphism of algebraic spaces. -/
@[stacks 085I "part (2): the morphism r_ψ is an isomorphism"]
theorem isIso_relativeMapSpaceHom
    (hiso : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      ∀ᶠ d : ℕ in atTop, IsIso ((hψ.hom T f).app (d : ℤ))) :
    IsIso hψ.relativeMapSpaceHom :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun Y =>
    (isIso_iff_bijective _).2 (hψ.bijective_app_relativeMapSpaceHom hiso Y)

/-- If every restriction of `ψ` is an isomorphism in all sufficiently large degrees then the maps
`θ : r_ψ^*𝒪_P(n) ⟶ 𝒪_Q(n)` of Stacks 085F are isomorphisms, over every scheme point `(T, f)` of the
base. -/
@[stacks 085I "part (3): the maps θ_n : r_ψ^*𝒪_P(n) ⟶ 𝒪_Q(n) on the twists of the two relative
Projs are isomorphisms, over every scheme point of the base — which is the assertion for θ
itself, θ being characterized by Tag 085F as having exactly those restrictions"]
theorem isIso_relativeTwistSpaceMap_of_eventually_isIso
    (hiso : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      ∀ᶠ d : ℕ in atTop, IsIso ((hψ.hom T f).app (d : ℤ)))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) (n : ℤ) :
    IsIso (hψ.relativeTwistSpaceMap T f n) :=
  Stacks.AlgebraicGeometry.Tag07ZGTwist.isIso_relativeTwistMap_of_eventually_isIso
    (hψ.hom T f) (hiso T f) n

end RelativeProjHomPoints

end AlgebraicGeometry.Space

end
