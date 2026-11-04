module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.RelativeProj
public import StacksFrontier.AlgebraicGeometry.NestedCocycleReduction.Basic
public import StacksFrontier.AlgebraicGeometry.ProjInclusionDegreeSection.Basic

/-!
# Tag 01NO's nested twist comparison on the homogeneous global sections

`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNested` is, for a nested pair
`W ⊆ U` of affine opens of the base of a quasi-coherent graded algebra, Tag 01NO's twist comparison
as a morphism of sheaves of modules on the relative projective spectrum, and
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpNested` reads it as a local isomorphism.
This file computes that morphism on one family of sections: the direct image of the
global section of `𝒪(k)` attached to a homogeneous element of degree `k` of the graded ring of
sections over the larger open.

The answer is the one the rigidity hypothesis
`Stacks.AlgebraicGeometry.RelativeTwistRigidity.FixesResDegreeSections` asks for: the direct image
of the global section attached to the *restricted* element.

## Main definitions

* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.resTop`: the restriction of a global section of
  a twist to an open, written as a function of the open, so that both sides of the statements below
  have one name.

## Main results

* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.projInclusionTwistMap_degreeSection`: the
  **named** comparison morphism of Tag 01NO carries the pulled-back homogeneous global section to
  the homogeneous global section of the restricted element. This is
  `Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.composite_degreeSection` reassociated onto
  `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap`.
* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.unit_tail_eq`: **the regrouping, at the level of
  variables.** A morphism into a direct image followed by the two pseudofunctoriality factors and
  an isomorphism out of the restriction equals the unit of the *pullback* adjunction followed by
  that isomorphism's pullback part, followed by the two structural factors — on the hypothesis
  that the morphism and that isomorphism compose to the pullback unit, which for the restriction
  adjunction's unit is `restrictUnit_comp_map_trans`. Every factor is a variable; see its
  implementation note for why the unit may not be written out.
* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNestedTail_eq'`: the three tail factors of
  the comparison written out, supplied to `unit_tail_eq` as its own equation.
* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNested_eq`: that regrouping at the nested
  twist comparison, which is an instance of it and nothing more.
* `Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNested_degreeSection` and
  `cmpNested_resTop_degreeSection`: **the section computation.** Over *every* open of the
  relative Proj,
  the comparison carries the direct image of `degreeSection (A.grading U) k c` to the direct image
  of `degreeSection (A.grading W) k ⟨A.res h c, _⟩`.

## The route, and why it needs no transport

Three steps, all of them reassociations over results already in the library.

* `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap_eq` already identifies the
  named comparison morphism with the six-factor composite; the composite that
  `composite_degreeSection` speaks about is the same six factors bracketed as `3 + 3`, so the two
  are joined by one application of `CategoryTheory.Category.assoc` at the level of variables.
* `Stacks.AlgebraicGeometry.ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback` trades
  the unit of the restriction adjunction followed by `restrictFunctorIsoPullback` for the unit of
  the pullback adjunction. That is exactly the leading factor of `pushNested` against the leading
  factor of `restrictTwistIso`, so it applies with no hypothesis beyond the transition morphism
  being an open immersion.
* `AlgebraicGeometry.Scheme.Modules.pushforwardComp` and `pushforwardCongr` are components of
  natural isomorphisms, so the factor `restrictTwistIso` moves past them by one naturality square.

**The statement is at an arbitrary open and needs no transport.** Both sides are restrictions of a
*global* section, and the only thing done to them is restriction along inclusions of opens; those
compose, and morphisms of opens are unique, so every bracketing of the restrictions collapses by
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.map_map_eq_map`. In particular nothing here asks
that `chart W ⁻¹ᵁ (toBase ⁻¹ᵁ W)` be `⊤` — which is true but only propositionally, and is where an
earlier plan for this computation was blocked.

Invertibility of the comparison is not used and no containment hypothesis appears: the identity
holds over every open of the relative Proj, and the containment enters only when the statement is
read through `cmpNested`, which is defined only over the inverse image of the smaller open.

## Implementation notes

Every structural step is an **application** of a lemma stated with the schemes, the morphisms and
the modules all variables; none is a `rfl` at the concrete instance, and `rw` is used only inside
such generic lemmas. That is the discipline the implementation notes of `RelativeProj.lean` record
as forced here, and it is why the reassociation is taken from
`Stacks.AlgebraicGeometry.ProjInclusionTwist.comp₃_comp`, stated at the level of variables:
the same regrouping done by `rw` at the concrete instance fails its motive check,
the error naming the two spellings of the structure sheaf of a projective spectrum.

`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNested_def` is the one delta step taken at the
concrete instance; it unfolds the definition of `pushNested` and nothing else, so it asks for no
reduction of `AlgebraicGeometry.Scheme.Modules.pullback`.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjInclusionDegreeSection
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.PullbackUnit
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.ChartTransRelativeProj

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local implicit_reducible]
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w

/-! ### Restriction and the direct image, at the level of variables -/

/-- **Two restrictions of a section, one after the other, are one restriction.** The three
inclusions are not assumed related: morphisms between opens are unique, so any morphism from the
first open to the third is their composite. -/
public theorem map_map_eq_map {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    (N : PresheafOfModules.{u} 𝒪) {A B D : Opens X} (a : op A ⟶ op B) (b : op B ⟶ op D)
    (c : op A ⟶ op D) (x : N.obj (op A)) : N.map b (N.map a x) = N.map c x :=
  (N.map_comp_apply a b x).symm.trans (N.congr_map_apply (Subsingleton.elim _ _) x)

/-- Restriction along two inclusions between the same pair of opens agrees. -/
public theorem map_eq_map {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    (N : PresheafOfModules.{u} 𝒪) {A B : Opens X} (a b : op A ⟶ op B) (x : N.obj (op A)) :
    N.map a x = N.map b x :=
  N.congr_map_apply (Subsingleton.elim _ _) x

/-- The direct image of a morphism of sheaves of modules, read on sections: a section of the direct
image over an open *is* a section of the module over the preimage, and the direct image of a
morphism acts there as the morphism itself. -/
public theorem pushforward_map_val_app {X Y : Scheme.{u}} (f : Y ⟶ X) {M N : Y.Modules}
    (φ : M ⟶ N) (V : X.Opens)
    (x : ((Scheme.Modules.pushforward f).obj M).val.obj (op V)) :
    ((Scheme.Modules.pushforward f).map φ).val.app (op V) x = φ.val.app (op (f ⁻¹ᵁ V)) x :=
  rfl

/-- **The pseudofunctoriality isomorphism of the direct image is the identity on sections.** The
sections of the direct image along a composite over an open are the sections of the module over the
iterated preimage, on the nose. -/
public theorem pushforwardComp_app_hom_val_app {X Y Z : Scheme.{u}} (p : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) (V : Z.Opens)
    (x : ((Scheme.Modules.pushforward p ⋙ Scheme.Modules.pushforward g).obj M).val.obj (op V)) :
    (((Scheme.Modules.pushforwardComp p g).app M).hom).val.app (op V) x = x :=
  rfl

/-- **The congruence isomorphism of the direct images along two equal morphisms is a restriction
map on sections**, between the two preimages — which are equal opens. -/
public theorem pushforwardCongr_app_hom_val_app {X Y : Scheme.{u}} {f g : X ⟶ Y} (hf : f = g)
    (M : X.Modules) (V : Y.Opens) (y : M.val.obj (op (f ⁻¹ᵁ V))) :
    (((Scheme.Modules.pushforwardCongr hf).app M).hom).val.app (op V) y =
      M.val.map (eqToHom (congrArg (fun k : X ⟶ Y => k ⁻¹ᵁ V) hf).symm).op y :=
  rfl

/-- **The two structural factors of the comparison move past a factor on the chart module.** This
is one naturality square of the composite natural isomorphism
`pushforwardComp ≪≫ pushforwardCongr`, which identifies the iterated direct image with the direct
image along the composite morphism. -/
public theorem pushforwardTail_naturality {X Y Z : Scheme.{u}} (p : X ⟶ Y) (g : Y ⟶ Z)
    {f : X ⟶ Z} (htr : p ≫ g = f) {M N : X.Modules} (ρ : M ⟶ N) :
    ((Scheme.Modules.pushforwardComp p g).hom.app M ≫
          (Scheme.Modules.pushforwardCongr htr).hom.app M) ≫
        (Scheme.Modules.pushforward f).map ρ =
      (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward p).map ρ) ≫
        ((Scheme.Modules.pushforwardComp p g).hom.app N ≫
          (Scheme.Modules.pushforwardCongr htr).hom.app N) :=
  ((Scheme.Modules.pushforwardComp p g ≪≫
    Scheme.Modules.pushforwardCongr htr).hom.naturality ρ).symm

/-- **The two structural factors, on sections, carry a restriction to a restriction.** The first is
the identity there and the second is a restriction map between two equal opens. -/
public theorem pushforwardTail_hom_val_app_map {X Y Z : Scheme.{u}} (p : X ⟶ Y) (g : Y ⟶ Z)
    {f : X ⟶ Z} (htr : p ≫ g = f) (N : X.Modules) (V : Z.Opens) {T : X.Opens}
    (a : op T ⟶ op (p ⁻¹ᵁ (g ⁻¹ᵁ V))) (b : op T ⟶ op (f ⁻¹ᵁ V)) (t : N.val.obj (op T)) :
    ((((Scheme.Modules.pushforwardComp p g).app N).hom ≫
        ((Scheme.Modules.pushforwardCongr htr).app N).hom)).val.app (op V) (N.val.map a t) =
      N.val.map b t := by
  refine Eq.trans (comp_app_of _ _ V rfl) ?_
  refine Eq.trans (congrArg
    ((((Scheme.Modules.pushforwardCongr htr).app N).hom).val.app (op V))
    (pushforwardComp_app_hom_val_app p g N V (N.val.map a t))) ?_
  refine Eq.trans (pushforwardCongr_app_hom_val_app htr N V (N.val.map a t)) ?_
  exact map_map_eq_map N.val a _ b t

/-- Equal morphisms of sheaves of modules agree on sections. -/
private theorem val_app_congr {X : Scheme.{u}} {M N : X.Modules} {φ ψ : M ⟶ N} (hφ : φ = ψ)
    (V : X.Opensᵒᵖ) (x : M.val.obj V) : φ.val.app V x = ψ.val.app V x :=
  congrArg (fun χ : M ⟶ N => χ.val.app V x) hφ

/-- **The unit of the restriction adjunction, followed by the identification of restriction with
the inverse image and any morphism out of it, is the unit of the pullback adjunction followed by
that morphism.** This is
`Stacks.AlgebraicGeometry.ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback` with the
trailing factor carried along. -/
public theorem restrictUnit_comp_map_comp {X Y : Scheme.{u}} (p : X ⟶ Y) [IsOpenImmersion p]
    (M : Y.Modules) {N : X.Modules} (τ : (Scheme.Modules.pullback p).obj M ⟶ N) :
    (Scheme.Modules.restrictAdjunction p).unit.app M ≫
        (Scheme.Modules.pushforward p).map
          ((Scheme.Modules.restrictFunctorIsoPullback p).hom.app M ≫ τ) =
      (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M ≫
        (Scheme.Modules.pushforward p).map τ := by
  rw [Functor.map_comp, ← Category.assoc,
    ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback p M]

/-- The same trade with the trailing morphism packaged as an isomorphism composed by `≪≫` rather
than by `≫`, which is the shape
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.restrictTwistIso` carries it in. -/
public theorem restrictUnit_comp_map_trans {X Y : Scheme.{u}} (p : X ⟶ Y) [IsOpenImmersion p]
    (M : Y.Modules) {N : X.Modules} (e : (Scheme.Modules.pullback p).obj M ≅ N) :
    (Scheme.Modules.restrictAdjunction p).unit.app M ≫
        (Scheme.Modules.pushforward p).map
          ((Scheme.Modules.restrictFunctorIsoPullback p).app M ≪≫ e).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M ≫
        (Scheme.Modules.pushforward p).map e.hom := by
  rw [Iso.trans_hom, Iso.app_hom]
  exact restrictUnit_comp_map_comp p M e.hom

/-- **The regrouping, at the level of variables.** For an open immersion `p`, a morphism `g` with
`p ≫ g = f`, a module `M` on the target of `p`, a module `R` on its source, a morphism
`η : M ⟶ p_* R`, an isomorphism `ε : R ≅ N`, an isomorphism `e` of the inverse image of `M` with
`N`, and the two pseudofunctoriality factors followed by the direct image of `ε` packaged as a
single isomorphism `t`, such that `η` followed by the direct image of `ε` is the unit of the
**pullback** adjunction followed by the direct image of `e`:

`η` pushed forward along `g` and then `t` equals the unit of the pullback adjunction followed by
the direct image of `e`, pushed forward along `g`, and then the two pseudofunctoriality factors.

This is the whole content of
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNested_eq`, with every scheme, morphism and
module a variable — which is the only place the regrouping is affordable.

**`η`, `R`, `ε`, `e` and `t` are variables, and not the restriction adjunction's unit and the three
tail factors written out, for a reason that is not generality.** The restriction unit is what
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNestedUnit` is defined to be, so stating this
lemma with the unit in place of `η` would read as the same theorem; but the comparison then
requires the two spellings to be identified at the concrete instance,
and they are not syntactically equal: the scheme `AlgebraicGeometry.Proj (A.grading U)` carries an
`AddSubgroupClass` instance argument whose proof the elaborator abstracts into an auxiliary
declaration *per module*, so the scheme as spelled where `pushNestedUnit` was defined and the
scheme as spelled here differ in that one proof constant, at every one of the forty-odd places the
scheme indexes a subterm. Each such place then needs a proof-irrelevance check, and each of those
needs the type of the abstracted proof — a `GradedRing` tower over a direct sum of sections.

With these as variables the concrete terms are **assigned** to them out of `pushNested`'s own
definition rather than compared against a second spelling, so the elaborator re-elaborates nothing;
that is why `pushNested_eq` leaves them to be inferred, supplies `t`'s own equation as the separate
`pushNestedTail_eq'`, and discharges the hypothesis afterwards by `refine`. -/
public theorem unit_tail_eq {X Y Z : Scheme.{u}} (p : X ⟶ Y) [IsOpenImmersion p] (g : Y ⟶ Z)
    {f : X ⟶ Z} (htr : p ≫ g = f) {M : Y.Modules} {R N : X.Modules}
    (η : M ⟶ (Scheme.Modules.pushforward p).obj R) (ε : R ≅ N)
    (e : (Scheme.Modules.pullback p).obj M ≅ N)
    (t : (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward p).obj R) ≅
          (Scheme.Modules.pushforward f).obj N)
    (ht : t = (Scheme.Modules.pushforwardComp p g).app R ≪≫
      (Scheme.Modules.pushforwardCongr htr).app R ≪≫
        (Scheme.Modules.pushforward f).mapIso ε)
    (hηε : η ≫ (Scheme.Modules.pushforward p).map ε.hom =
      (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M ≫
        (Scheme.Modules.pushforward p).map e.hom) :
    (Scheme.Modules.pushforward g).map η ≫ t.hom =
      (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M ≫
            (Scheme.Modules.pushforward p).map e.hom) ≫
        (((Scheme.Modules.pushforwardComp p g).app N).hom ≫
          ((Scheme.Modules.pushforwardCongr htr).app N).hom) := by
  subst ht
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc ((Scheme.Modules.pushforwardComp p g).hom.app R),
    pushforwardTail_naturality p g htr, ← Category.assoc, ← Functor.map_comp, hηε]

/-- The restriction of a global section of a twist to an open, as a function of the open. Both
sides of every statement below are of this form. -/
public abbrev resTop {R : Type u} {σ : Type w} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (m : ℤ) (T : Opens (ProjectiveSpectrum.top 𝒜))
    (t : (twistingSheaf 𝒜 m).val.obj (op ⊤)) : (twistingSheaf 𝒜 m).val.obj (op T) :=
  (twistingSheaf 𝒜 m).val.map (homOfLE (le_top : T ≤ ⊤)).op t

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (W U : S.Opens) (h : W ≤ U)
  (hW : IsAffineOpen W) (hU : IsAffineOpen U)

/-! ### Step one: the named comparison morphism on a homogeneous global section -/

/-- **Tag 01NO's named twist comparison carries the pulled-back homogeneous global section to the
homogeneous global section of the restricted element.**

`Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.composite_degreeSection` proves this for the
six-factor composite bracketed as three plus three, because at that bracketing the junction between
the composite-functor spelling and the iterated-image spelling costs nothing; and
`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap_eq` identifies the named
morphism with the same six factors associated to the right. The two are joined by one
reassociation, taken at the level of variables. -/
public theorem projInclusionTwistMap_degreeSection (k : ℕ) (c : (A.grading U) k) :
    (ProjInclusionTwist.projInclusionTwistMap A W U h hW hU (k : ℤ)).val.app (op ⊤)
        (pullbackSection (projInclusionMap A W U h hW hU)
          (twistingSheaf (A.grading U) (k : ℤ)) (degreeSection (A.grading U) k c)) =
      degreeSection (A.grading W) k ⟨A.res h c, (A.res h).map_mem c.2⟩ :=
  (val_app_congr
      ((ProjInclusionTwist.projInclusionTwistMap_eq A W U h hW hU (k : ℤ)).trans
        (ProjInclusionTwist.comp₃_comp _ _ _ _).symm) _ _).trans
    (composite_degreeSection A W U h hW hU k c)

/-! ### Step two: the direct image comparison, regrouped -/

/-- The comparison is the unit factor followed by the three tail factors. The one delta step taken
at the concrete instance. -/
public alias pushNested_def := Stacks.AlgebraicGeometry.NestedCocycleReduction.pushNested_eq

/-- **The three tail factors of the comparison, written out.** The one of the two delta steps at
the concrete instance that is cheap: no twist appears in the statement, only the restriction of
one and the named structural isomorphisms, so the two spellings of the projective spectrum that
`pushNestedTail_eq'` has to identify are the same term. It is stated apart from `pushNested_eq`
rather than inlined there so that the kernel checks the two separately.

The prime distinguishes it from
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNestedTail_eq`, the same identity with the
restricted twist spelled by `AlgebraicGeometry.Scheme.Modules.restrictFunctor` instead of by the
named `restrictedTwist` and `restrictTwistIso`; the two right-hand sides are different terms, so
they are different equations and both are kept. -/
public theorem pushNestedTail_eq' (n : ℤ) :
    pushNestedTail A W U h hW hU n =
      (Scheme.Modules.pushforwardComp (projInclusionMap A W U h hW hU)
            ((relativeProj A).chart U hU)).app (restrictedTwist A W U h hW hU n) ≪≫
        (Scheme.Modules.pushforwardCongr
              ((relativeProj A).chart_transition W U h hW hU)).app
            (restrictedTwist A W U h hW hU n) ≪≫
          (Scheme.Modules.pushforward ((relativeProj A).chart W hW)).mapIso
            (restrictTwistIso A W U h hW hU n) :=
  rfl

/-- **The nested comparison, with the unit of the pullback adjunction in front and the two
structural factors behind.**

This is the same morphism as `Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNested`: it is
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.unit_tail_eq` at the transition morphism of the
charts, the chart of the larger affine open and the chart compatibility, with the unit factor, the
restriction of the twist and Tag 01NO's twist isomorphism **left to be inferred** from
`pushNested`'s own definition, and the tail supplied as `pushNestedTail_eq'`. In this form the
whole content of the comparison on sections is Tag 01NO's named morphism applied to a
pulled-back section, which is what Tag 01MY computes.

The hypothesis of `unit_tail_eq` is discharged after the fact, by `refine`, so that its unit
factor is inferred from `pushNested` before `restrictUnit_comp_map_trans` is matched against it;
see that lemma's implementation note for why writing the unit out here does not work. -/
public theorem pushNested_eq (n : ℤ) :
    pushNested A W U h hW hU n =
      (Scheme.Modules.pushforward ((relativeProj A).chart U hU)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
                (projInclusionMap A W U h hW hU)).unit.app (twistingSheaf (A.grading U) n) ≫
            (Scheme.Modules.pushforward (projInclusionMap A W U h hW hU)).map
              (ProjInclusionTwist.projInclusionTwistIso A W U h hW hU n).hom) ≫
        (((Scheme.Modules.pushforwardComp (projInclusionMap A W U h hW hU)
              ((relativeProj A).chart U hU)).app (twistingSheaf (A.grading W) n)).hom ≫
          ((Scheme.Modules.pushforwardCongr
                ((relativeProj A).chart_transition W U h hW hU)).app
              (twistingSheaf (A.grading W) n)).hom) := by
  refine (pushNested_def A W U h hW hU n).trans
    (unit_tail_eq (projInclusionMap A W U h hW hU) ((relativeProj A).chart U hU)
      ((relativeProj A).chart_transition W U h hW hU) _ _ _ _
      (pushNestedTail_eq' A W U h hW hU n) ?_)
  exact restrictUnit_comp_map_trans _ _ _

/-! ### Step three: the section computation -/

/-- The leading factor of the regrouped comparison, on the direct image of a homogeneous global
section: the unit of the pullback adjunction carries the restricted global section to the
restriction of the pulled-back global section, by naturality, and Tag 01NO's named morphism then
lands on the global section attached to the restricted element. -/
public theorem pushNested_lead_degreeSection (k : ℕ) (c : (A.grading U) k)
    (V : (relativeProj A).scheme.Opens) :
    ((Scheme.Modules.pushforward ((relativeProj A).chart U hU)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
                (projInclusionMap A W U h hW hU)).unit.app
              (twistingSheaf (A.grading U) (k : ℤ)) ≫
            (Scheme.Modules.pushforward (projInclusionMap A W U h hW hU)).map
              (ProjInclusionTwist.projInclusionTwistIso A W U h hW hU
                (k : ℤ)).hom)).val.app (op V)
        (resTop (A.grading U) (k : ℤ) ((relativeProj A).chart U hU ⁻¹ᵁ V)
          (degreeSection (A.grading U) k c)) =
      (twistingSheaf (A.grading W) (k : ℤ)).val.map
          (homOfLE (le_top : projInclusionMap A W U h hW hU ⁻¹ᵁ
            ((relativeProj A).chart U hU ⁻¹ᵁ V) ≤ ⊤)).op
        (degreeSection (A.grading W) k ⟨A.res h c, (A.res h).map_mem c.2⟩) := by
  refine Eq.trans (pushforward_map_val_app ((relativeProj A).chart U hU) _ V _) ?_
  refine Eq.trans (comp_app_of _ _ ((relativeProj A).chart U hU ⁻¹ᵁ V) rfl) ?_
  refine Eq.trans (congrArg
      (((Scheme.Modules.pushforward (projInclusionMap A W U h hW hU)).map
        (ProjInclusionTwist.projInclusionTwistIso A W U h hW hU (k : ℤ)).hom).val.app
          (op ((relativeProj A).chart U hU ⁻¹ᵁ V)))
      (PresheafOfModules.naturality_apply
        ((Scheme.Modules.pullbackPushforwardAdjunction
            (projInclusionMap A W U h hW hU)).unit.app
          (twistingSheaf (A.grading U) (k : ℤ))).val
        (homOfLE (le_top : (relativeProj A).chart U hU ⁻¹ᵁ V ≤ ⊤)).op
        (degreeSection (A.grading U) k c))) ?_
  refine Eq.trans (pushforward_map_val_app (projInclusionMap A W U h hW hU) _ _ _) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply
    (ProjInclusionTwist.projInclusionTwistIso A W U h hW hU (k : ℤ)).hom.val _ _) ?_
  refine Eq.trans (congrArg ((twistingSheaf (A.grading W) (k : ℤ)).val.map _)
    (projInclusionTwistMap_degreeSection A W U h hW hU k c)) ?_
  exact map_eq_map _ _ _ _

/-- **The nested comparison on the direct image of a homogeneous global section.** For affine opens
`W ⊆ U` of the base, a degree `k` and a homogeneous element `c` of degree `k` of the graded ring of
sections over `U`, the comparison carries the direct image of `degreeSection (A.grading U) k c` to
the direct image of `degreeSection (A.grading W) k ⟨A.res h c, _⟩`, over **every** open of the
relative projective spectrum.

Neither a containment nor invertibility is used: the identity is about the morphism `pushNested`,
which is defined everywhere. -/
public theorem pushNested_degreeSection (k : ℕ) (c : (A.grading U) k)
    (V : (relativeProj A).scheme.Opens) :
    (pushNested A W U h hW hU (k : ℤ)).val.app (op V)
        (resTop (A.grading U) (k : ℤ) ((relativeProj A).chart U hU ⁻¹ᵁ V)
          (degreeSection (A.grading U) k c)) =
      resTop (A.grading W) (k : ℤ) ((relativeProj A).chart W hW ⁻¹ᵁ V)
        (degreeSection (A.grading W) k ⟨A.res h c, (A.res h).map_mem c.2⟩) := by
  refine Eq.trans (val_app_congr (pushNested_eq A W U h hW hU (k : ℤ)) _ _) ?_
  refine Eq.trans (comp_app_of _ _ V
    (pushNested_lead_degreeSection A W U h hW hU k c V)) ?_
  exact pushforwardTail_hom_val_app_map (projInclusionMap A W U h hW hU)
    ((relativeProj A).chart U hU) ((relativeProj A).chart_transition W U h hW hU)
    (twistingSheaf (A.grading W) (k : ℤ)) V _ _ _

/-- **Tag 01NO's twist comparison for a nested pair of affine opens, on the homogeneous global
sections.** The statement the relative rigidity hypothesis
`Stacks.AlgebraicGeometry.RelativeTwistRigidity.FixesResDegreeSections` is discharged from: over an
open of the relative Proj inside the inverse image of the smaller affine open, the component of
`cmpNested` carries the direct image of the global section attached to a homogeneous element of the
graded ring of sections over the larger open to the direct image of the global section attached to
its restriction.

Both restriction maps are `resTop`, the restriction from the top open in the twisting sheaf on
the chart.  `Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpNested_degreeSection` is the
same computation with the restriction taken along an arbitrary morphism of opens in the direct
images on the relative Proj; neither statement is an instance of the other as it stands. -/
public theorem cmpNested_resTop_degreeSection (k : ℕ) (c : (A.grading U) k)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W) :
    (cmpNested A W U h hW hU (k : ℤ)).app V hV
        (resTop (A.grading U) (k : ℤ) ((relativeProj A).chart U hU ⁻¹ᵁ V)
          (degreeSection (A.grading U) k c)) =
      resTop (A.grading W) (k : ℤ) ((relativeProj A).chart W hW ⁻¹ᵁ V)
        (degreeSection (A.grading W) k ⟨A.res h c, (A.res h).map_mem c.2⟩) :=
  (cmpNested_app A W U h hW hU (k : ℤ) V hV _).trans
    (pushNested_degreeSection A W U h hW hU k c V)

end Stacks.AlgebraicGeometry.ChartTransRelativeProj

end
