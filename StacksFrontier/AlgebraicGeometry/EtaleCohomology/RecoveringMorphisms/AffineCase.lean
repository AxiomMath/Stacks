module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingTerminalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.MorphismsGeneral
public import StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing

/-!
# Recovering a morphism of affine schemes from its ring map on global functions

Stacks 04I6 says that for affine schemes `X` and `Y`, a morphism of *locally* ringed topoi
`(g, g^♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` is 2-isomorphic to `(f_small, f_small^♯)`
for a unique morphism of schemes `f : X ⟶ Y`.

The source's proof opens by passing to global sections: since `Y = Spec B` and `X = Spec A` are
affine, `B = Γ(Y_étale, 𝒪_Y)` and `A = Γ(X_étale, 𝒪_X)`, so `g^♯` induces a ring map
`φ : B ⟶ A`, and `f := Spec φ` is the morphism of schemes that the lemma asserts exists.  This
file formalizes that opening paragraph and nothing more.  Its *scheme-theoretic* half is the
passage from a ring map on global functions to a morphism of schemes, together with its
bijectivity when the target is affine: that is where the hypothesis "`Y` is affine" is used in
the source, and it is the step that makes the candidate `f` both exist and be unique *given*
`φ`.  The *topos-theoretic* half is the production of `φ` from `g^♯`, which is
`AlgebraicGeometry.RingedToposHom.globalSectionsMap` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingTerminalSections`; the two are
composed in `Stacks.EtaleCohomology.existsUnique_schemeHom_appTop_eq_globalSectionsMap`.

The remainder of Stacks 04I6 is formalized elsewhere, so this file carries **no**
`@[stacks 04I6]` tag; see the "Where the rest of Stacks 04I6 lives" section below.

## Main definitions

* `Stacks.EtaleCohomology.schemeHomOfAppTop` — the morphism of schemes `X ⟶ Y` attached to a
  ring map `Γ(Y, ⊤) ⟶ Γ(X, ⊤)` when `Y` is affine, namely `Spec φ` read through the canonical
  isomorphism `Y ≅ Spec Γ(Y, ⊤)`.
* `Stacks.EtaleCohomology.schemeHomEquivAppTop` — the resulting bijection between morphisms of
  schemes `X ⟶ Y` and ring maps `Γ(Y, ⊤) ⟶ Γ(X, ⊤)`, for `Y` affine.

## Main results

* `Stacks.EtaleCohomology.appTop_schemeHomOfAppTop` and
  `Stacks.EtaleCohomology.schemeHomOfAppTop_appTop` — the two round trips: the attached
  morphism induces the given ring map on global functions, and a morphism of schemes into an
  affine scheme is recovered from the ring map it induces.
* `Stacks.EtaleCohomology.existsUnique_schemeHom_appTop_eq` — for `Y` affine there is a *unique*
  morphism of schemes `X ⟶ Y` inducing a prescribed ring map on global functions.  This is the
  form in which the source's opening step is used: it produces the candidate `f` of Stacks 04I6
  and shows that the candidate is pinned down by `φ`.
* `Stacks.EtaleCohomology.existsUnique_schemeHom_appTop_eq_globalSectionsMap` — the same
  statement with the ring map `φ` *extracted from* a morphism `(g, g^♯)` of small étale ringed
  topoi rather than given, which is the form the source's first paragraph has.

The second step of the source's proof, the equalizer presentation of the representable sheaf
`h_V`, is in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/RepresentableEqualizer.lean`.

## Where the rest of Stacks 04I6 lives

Write `A = Γ(X, ⊤)`, `B = Γ(Y, ⊤)`.  The source's argument, after the step formalized here, is:

1. `g^♯` has to be evaluated at the *terminal object* of the small étale site of
   `Y` and the result identified, as a ring, with `A`: one needs
   `(g_*𝒪_X)(𝟙_Y) ≅ Γ(X_étale, 𝒪_X) = A` for the direct image along a morphism of *topoi*.
   This is not a site-level restriction — `AlgebraicGeometry.RingedToposHom.fSharp` lands in
   `Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor`, whose sections at an object of
   the site carry a *transported* ring structure.  The comparison is
   `MorphismOfTopoi.pushforwardCommRingTerminalSectionsIso` and the resulting ring map on
   global functions is `AlgebraicGeometry.RingedToposHom.globalSectionsMap`, both in
   `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingTerminalSections`; this file's
   `Stacks.EtaleCohomology.existsUnique_schemeHom_appTop_eq_globalSectionsMap` is that step
   composed with the bijection above, i.e. the whole of the source's first paragraph.
2. For each affine `V = Spec C` étale over `Y`, with a standard presentation
   `C = B[x₁, …, xₙ]/(P₁, …, Pₙ)` whose Jacobian determinant is invertible, the representable
   sheaf `h_V` on `Y_étale` is the equalizer of two maps `∏ᵢ 𝒪_Y ⇉ ∏ⱼ 𝒪_Y`.  This is
   `Stacks.EtaleCohomology.homOverEquivSolutions` in
   `StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/RepresentableEqualizer.lean`:
   the `Y`-morphisms `U ⟶ V` are the tuples `a : Fin n → Γ(U, ⊤)` at which every `Pⱼ` vanishes,
   naturally in `U` (`Stacks.EtaleCohomology.homOverEquivSolutions_naturality`), and the
   vanishing condition is the equation between the two maps
   (`Stacks.EtaleCohomology.isSolution_iff_eq_zero`).  Its ring-theoretic core is
   `MvPolynomial.quotientSpanRangeHomOverEquiv` in
   `StacksFrontier/RingTheory/Etale/StandardPresentationSolutions.lean`.  The presentation itself is
   produced, which is Stacks 00U9, by
   `AlgebraicGeometry.ProEtale.exists_fin_algEquiv_quotientSpanRange_of_etale` in
   `StacksFrontier/AlgebraicGeometry/ProEtale/IndEtaleConstruction/Presentation.lean` — carrying no
   faithful-flatness hypothesis, unlike
   `AlgebraicGeometry.ProEtale.exists_standardEtalePresentation_of_etale_faithfullyFlat` beside
   it — and assembled over a chart in
   `.RecoveringMorphisms.PresentationExistence`.
3. Exactness of `g⁻¹` then produces the comparison `g⁻¹h_V ⟶ h_{X ×_Y V}`, and the claim that
   it is an isomorphism is checked on stalks.  This is the only place the *locally* ringed
   hypothesis enters: it makes `(g^♯)_p` a local homomorphism of strictly henselian local
   rings, and the conclusion is Stacks 04GX (solutions of étale equations over a strictly
   henselian local ring).  The comparison is built in
   `.RecoveringMorphisms.ComparisonNatural` out of the ring homomorphism
   `AlgebraicGeometry.comparisonRingHom`, which is defined at every global function on `V` at
   once rather than on the `n` coordinates; its geometric fibres are identified with the
   solution sets in `.RecoveringMorphisms.ComparisonFiberSolutionMap` and
   `.RecoveringMorphisms.GeometricFiberSolutions`, and it is an isomorphism at every affine
   chart by `.RecoveringMorphisms.AffineComparisonIsIso`.  The stalk-testing criterion used is
   `AlgebraicGeometry.isIso_iff_forall_bijective_geometricSheafFiber` in
   `StacksFrontier/AlgebraicGeometry/EtaleCohomology/StalkIsomorphismCriterion.lean`, the
   type-valued companion of
   `AlgebraicGeometry.GeometricPoint.isIso_iff_forall_bijective_stalkFunctor`; and Stacks 04GX
   itself is `bijOn_solutions_of_etale` in
   `StacksFrontier/RingTheory/Henselian/EtaleLifting.lean` (**root** namespace, not
   `AlgebraicGeometry`), read on points of a presentation as
   `MvPolynomial.bijective_homOverMap_of_etale`.  For the locality of `(g^♯)_p` see step (3')
   below.
4. Functoriality of those isomorphisms in `V`, then `f_{small,*} ≅ g_*` by Yoneda on the
   dense subsite of affine étale charts, and finally the compatibility of `f_small^♯` with
   `g^♯` on sections over an affine `V`.  The transport from the affine charts to all of
   `Y_étale` is `.RecoveringMorphisms.AffineComparisonAssembly`, resting on Stacks 04HR
   (`AlgebraicGeometry.SmallAffineEtale.inclusion_isSpecialCocontinuous`); the assembly of a
   2-isomorphism from an isomorphism of direct images together with the agreement of the two
   structure maps is `.RecoveringMorphisms.ExistenceFromAffineComparison`, and the closing
   agreement of the structure maps is `.RecoveringMorphisms.AffineExistence`.
5. The uniqueness half is Stacks 04LW (faithfulness of `X ↦ (X_étale, 𝒪_X)`), which is a
   separate tag, stated for schemes in `StacksDraft.AlgebraicGeometry.EtaleCohomology`
   `.RecoveringMorphisms.Faithful` as `AlgebraicGeometry.eq_of_smallEtale_twoIso`.

Step (3') — extracting from the *locally* ringed hypothesis the locality of `(g^♯)_p` — is
proved at independent universes, and so applies to the small étale site.  It is the composite of
`AlgebraicGeometry.RingedSite.HomGeneral.reflectsUnitsObj_of_isLocallyRinged`, which is
Stacks 04H9 in the direction (1) ⇒ (3) in the `ReflectsUnitsObj` formulation
(`StacksFrontier/CategoryTheory/Sites/Modules/LocallyRingedSites/IsLocallyRingedCriterion.lean`),
with `AlgebraicGeometry.RingedTopos.isLocalHom_sheafFiber_of_reflectsUnitsObj` in
`StacksFrontier/CategoryTheory/Sites/Modules/LocallyRingedSites/StalkReflectsUnits.lean`, which
turns reflection of units at a point of the site into locality of the fibre ring map there.  The
self-contained formulation of
`StacksFrontier/CategoryTheory/Sites/Modules/LocallyRingedSites/StalkCriterion.lean`, whose ringed
topoi have `C : Type u` with `Category.{u} C` and therefore do not include the small étale site,
is not the only route.

The uniqueness half of Stacks 04I6 is proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedToposTwoIso` as
`AlgebraicGeometry.eq_of_twoIso_smallEtaleRingedToposHom`, and the morphism of small étale ringed
topoi `(f_small, f_small^♯)` of a morphism of *schemes* which that statement names is
`AlgebraicGeometry.smallEtaleRingedToposHom` of the same file.  The existence half, and the tag in
full, are `AlgebraicGeometry.exists_schemeHom_twoIso_of_isLocallyRinged` and
`AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_isLocallyRinged` in
`.RecoveringMorphisms.AffineExistence`, which is where the `@[stacks 04I6]` tag sits.

The bijection formalized here is the affine-target form of Stacks 01I1 (a morphism into an
affine scheme is a ring map on global functions), restricted to a scheme source. Stacks 01I1
itself is `AlgebraicGeometry.bijective_Γ_map_op_of_isAffine` in
`StacksFrontier/AlgebraicGeometry/Schemes/MorphismsToAffine.lean`, which carries the tag and states
it at the source's generality, for a locally ringed space source. The form here is kept because
it is the `Equiv` and `∃!` shapes this file's argument consumes.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.EtaleCohomology

section AffineTarget

variable (X Y : Scheme.{u})

/-- The morphism of schemes `X ⟶ Y` attached to a ring map `φ : Γ(Y, ⊤) ⟶ Γ(X, ⊤)` when `Y` is
affine: it is `Spec φ`, prefixed by the canonical morphism `X ⟶ Spec Γ(X, ⊤)` and postfixed by
the inverse of the canonical isomorphism `Y ≅ Spec Γ(Y, ⊤)`.

This is the morphism `f = Spec(φ)` of the first paragraph of the proof of Stacks 04I6. -/
def schemeHomOfAppTop [IsAffine Y] (φ : Γ(Y, ⊤) ⟶ Γ(X, ⊤)) : X ⟶ Y :=
  X.toSpecΓ ≫ Spec.map φ ≫ Y.isoSpec.inv

/-- On global functions, `Stacks.EtaleCohomology.schemeHomOfAppTop` induces the ring map it was
built from. -/
@[simp]
theorem appTop_schemeHomOfAppTop [IsAffine Y] (φ : Γ(Y, ⊤) ⟶ Γ(X, ⊤)) :
    (schemeHomOfAppTop X Y φ).appTop = φ := by
  have h : Y.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(Y, ⊤)).hom = CategoryStruct.id _ := by
    simp only [Scheme.isoSpec, asIso_inv, Scheme.Hom.inv_appTop, Scheme.toSpecΓ_appTop,
      IsIso.inv_hom_id]
  rw [schemeHomOfAppTop, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    Scheme.toSpecΓ_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, reassoc_of% h]

/-- A morphism of schemes into an affine scheme is recovered from the ring map it induces on
global functions. -/
@[simp]
theorem schemeHomOfAppTop_appTop [IsAffine Y] (f : X ⟶ Y) :
    schemeHomOfAppTop X Y f.appTop = f := by
  rw [schemeHomOfAppTop, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
  simp [Scheme.isoSpec]

/-- **For an affine target, a morphism of schemes is the same thing as a ring map on global
functions.** The bijection is `f ↦ f^♯` on global sections, with inverse
`Stacks.EtaleCohomology.schemeHomOfAppTop`.

This is the step of Stacks 04I6 that uses affineness of `Y`: it turns the ring map which a
morphism of ringed topoi induces on global functions into a morphism of schemes, and shows that
no other morphism of schemes induces the same ring map. -/
def schemeHomEquivAppTop [IsAffine Y] : (X ⟶ Y) ≃ (Γ(Y, ⊤) ⟶ Γ(X, ⊤)) where
  toFun f := f.appTop
  invFun φ := schemeHomOfAppTop X Y φ
  left_inv f := schemeHomOfAppTop_appTop X Y f
  right_inv φ := appTop_schemeHomOfAppTop X Y φ

/-- The bijection of `Stacks.EtaleCohomology.schemeHomEquivAppTop` sends a morphism of schemes
to the ring map it induces on global functions. -/
@[simp]
theorem schemeHomEquivAppTop_apply [IsAffine Y] (f : X ⟶ Y) :
    schemeHomEquivAppTop X Y f = f.appTop := rfl

/-- The inverse of the bijection of `Stacks.EtaleCohomology.schemeHomEquivAppTop` is the
construction `Spec φ` of `Stacks.EtaleCohomology.schemeHomOfAppTop`. -/
@[simp]
theorem schemeHomEquivAppTop_symm_apply [IsAffine Y] (φ : Γ(Y, ⊤) ⟶ Γ(X, ⊤)) :
    (schemeHomEquivAppTop X Y).symm φ = schemeHomOfAppTop X Y φ := rfl

/-- **The candidate morphism of Stacks 04I6 exists and is unique.** For `Y` affine and a
prescribed ring map `φ` on global functions there is exactly one morphism of schemes `X ⟶ Y`
inducing `φ`. -/
theorem existsUnique_schemeHom_appTop_eq [IsAffine Y] (φ : Γ(Y, ⊤) ⟶ Γ(X, ⊤)) :
    ∃! f : X ⟶ Y, f.appTop = φ :=
  ⟨schemeHomOfAppTop X Y φ, appTop_schemeHomOfAppTop X Y φ, fun f hf => by
    rw [← hf, schemeHomOfAppTop_appTop]⟩

end AffineTarget

/-! ### Global sections on the small étale site

The source's `A = Γ(X_étale, 𝒪_X)` and `B = Γ(Y_étale, 𝒪_Y)`: the global sections of the
structure sheaf of the small étale site are the sections over the terminal object `S / S` of
that site, and those are the global functions on `S` — definitionally, because the structure
presheaf of the small étale site is `U ↦ Γ(U, ⊤)` and the terminal object is `𝟙 S`. -/

section SmallEtale

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`Γ(S_étale, 𝒪_S) = Γ(S, ⊤)`.** The sections of the structure sheaf of the small étale
ringed site of `S` over the terminal object `S / S` of that site are the global functions
on `S`.

This is one of the two identifications with which the proof of Stacks 04I6 begins; it holds by
definitional unfolding, since the structure presheaf of the small étale site sends an étale
chart to its ring of global functions and the terminal chart is `𝟙 S`. -/
theorem smallEtaleRingedSite_structureSheaf_obj_final :
    (smallEtaleRingedSite B S hS).O.obj.obj (Opposite.op (SmallEtale.final B S hS)) =
      Γ(S, ⊤) :=
  rfl

end SmallEtale

/-- **The opening step of the proof of Stacks 04I6, assembled.** Let `X` and `Y` be schemes in a
big étale site, with `Y` affine, and let `φ` be a homomorphism from the ring of global sections
of the structure sheaf of the small étale site of `Y` to that of `X` — this is the ring map
`φ : B ⟶ A` which the source extracts from `g^♯`.  Then there is exactly one morphism of schemes
`f : X ⟶ Y` inducing `φ` on global functions.

That `φ`, whose source and target are *small étale* global sections, is accepted as a map
`Γ(Y, ⊤) ⟶ Γ(X, ⊤)` without any transport is the content of
`Stacks.EtaleCohomology.smallEtaleRingedSite_structureSheaf_obj_final`.

This produces the candidate morphism `f = Spec φ` of Stacks 04I6 and shows it is pinned down by
`φ`.  It does **not** prove Stacks 04I6: nothing here relates `(g, g^♯)` to
`(f_small, f_small^♯)` — see the module docstring.  For the form in which `φ` is extracted from
`g^♯` rather than supplied, see
`Stacks.EtaleCohomology.existsUnique_schemeHom_appTop_eq_globalSectionsMap`. -/
theorem existsUnique_schemeHom_appTop_eq_of_smallEtaleGlobalSections
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (X Y : Scheme.{u})
    (hX : B.Contains X) (hY : B.Contains Y) [IsAffine Y]
    (φ : (smallEtaleRingedSite B Y hY).O.obj.obj (Opposite.op (SmallEtale.final B Y hY)) ⟶
      (smallEtaleRingedSite B X hX).O.obj.obj (Opposite.op (SmallEtale.final B X hX))) :
    ∃! f : X ⟶ Y, f.appTop = φ :=
  existsUnique_schemeHom_appTop_eq X Y φ

/-! ### Extracting the ring map from a morphism of ringed topoi

The ring map `φ : B ⟶ A` of the source's first paragraph is not given; it is *produced* from
`g^♯`.  The general construction is
`AlgebraicGeometry.RingedToposHom.globalSectionsMap`: evaluate `g^♯ : 𝒪_Y ⟶ g_*𝒪_X` over the
terminal object of the site presenting the target and compose with the comparison
`Γ(⊤, g_*𝒪_X) ≅ Γ(⊤, 𝒪_X)` of
`MorphismOfTopoi.pushforwardCommRingTerminalSectionsIso`.  Applied to the small étale ringed
topoi this yields the `φ` the previous section consumes. -/

section RingedTopos

variable (B : AlgebraicGeometry.BigEtaleSite.{u})

/-- **The opening step of the proof of Stacks 04I6, with the ring map extracted from `g^♯`.**
Let `X` and `Y` be schemes in a big étale site, with `Y` affine, and let `(g, g^♯)` be a
morphism of the small étale *ringed* topoi of `X` and `Y`.  Then there is exactly one morphism
of schemes `f : X ⟶ Y` inducing, on global functions, the ring map that `g^♯` induces on global
sections of the structure sheaves.

That ring map is `φ : B ⟶ A` and that `f` is `Spec φ` in the source's notation.  This does
**not** prove Stacks 04I6: nothing here says that `(g, g^♯)` is 2-isomorphic to
`(f_small, f_small^♯)`, which is the assertion of the tag; see the module docstring for what
remains.  Note also that the source's hypothesis is a morphism of *locally* ringed topoi, which
is strictly more than the `AlgebraicGeometry.RingedToposHom` taken here — the locality is not
used by this step, and is used by the source only in the stalk computation of step (3) of the
module docstring. -/
theorem existsUnique_schemeHom_appTop_eq_globalSectionsMap (X Y : Scheme.{u})
    (hX : B.Contains X) (hY : B.Contains Y) [IsAffine Y]
    (g : AlgebraicGeometry.RingedToposHom
      (RingedSite.toRingedTopos (smallEtaleRingedSite B X hX))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y hY))) :
    ∃! f : X ⟶ Y, f.appTop =
      g.globalSectionsMap (SmallEtale.finalIsTerminal B X hX)
        (SmallEtale.finalIsTerminal B Y hY) :=
  existsUnique_schemeHom_appTop_eq_of_smallEtaleGlobalSections B X Y hX hY _

end RingedTopos

end Stacks.EtaleCohomology

end
