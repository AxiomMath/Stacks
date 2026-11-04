module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeTwist
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumExists
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The base change of the canonical tautological datum is the canonical tautological datum

Let `g : X' ⟶ X`, let `E` be a quasi-coherent `𝒪_X`-module, `E'` a quasi-coherent
`𝒪_{X'}`-module and `hE : E' ≅ g^*E`. Write `b : 𝐏(E') ⟶ 𝐏(E)` for
`Stacks.RelativeProj.projectiveBundleBaseChange`.

`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/TautologicalDatumExists.lean` builds the
canonical tautological datum `Stacks.RelativeProj.tautologicalDatum` of `𝐏(F)` for every
quasi-coherent `F`, by transporting the `𝒪(1)` of the `SheafGradedAlgebra` substrate
along `Stacks.ProjectiveBundle.presentationIso`.
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/TautologicalBaseChange.lean` pulls an arbitrary
datum on `𝐏(E)` back along `b` to one on `𝐏(E')`, as
`Stacks.RelativeProj.TautologicalDatum.baseChange`, and its implementation notes single out
exactly the statement that the base-changed datum is `𝐏(E')`'s own canonical one.

**This file supplies that identification**, so that Tag 0B3V's base-change clause — which is
proved for the base-changed datum in `TautologicalBaseChange.lean` and, for the bijection, in
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/SectionsBaseChange.lean` — can be read at the
canonical datum on both bundles.

## Main definitions

* `Stacks.RelativeProj.symTwistBaseChangeIso`: the comparison
  `(baseChangeHom)^*𝒪(1) ≅ 𝒪(1)` on the `SheafGradedAlgebra` substrate. This is
  `Stacks.Chow.GenuineChern.twistPullbackIso` with its chart hypothesis discharged by
  `Stacks.ProjectiveBundle.exists_chart_baseChangeHom`, so it is unconditional in `g` and `E`.
* `Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso`: **the comparison
  `b^*𝒪_{𝐏(E)}(1) ≅ 𝒪_{𝐏(E')}(1)`** on `Stacks.RelativeProj.projectiveBundle`, the previous one
  transported along the two presentation comparisons.

## Main results

* `Stacks.Modules.squarePaste_coherence`: **the pasting coherence of the pullback pseudofunctor
  at two commuting squares**, stated for arbitrary schemes with no projective bundle in sight.
  It is `Stacks.Modules.sectionSquare_coherence` with its two identity morphisms replaced by
  arbitrary ones, and like it the proof is three instances of
  `Stacks.Modules.pullbackComp_congr_assoc`, here with no unitality coherence needed. It is the
  last input the compatibility of the comparison below with the two universal surjections
  requires; see `Not done here`.
* `Stacks.RelativeProj.projectiveBundleBaseChange_comp_bundlePresentationIso_inv`: the square
  relating the base-change morphism of the two substrates, `b ≫ c⁻¹ = (c')⁻¹ ≫ h`. This is what
  the transport runs along, and it is immediate from
  `Stacks.ProjectiveBundle.baseChangeHom` being *defined* as `c' ≫ b ≫ c⁻¹`.
* `Stacks.RelativeProj.symTwistBaseChangeIso_spec`: the comparison on the `SheafGradedAlgebra`
  substrate carries the pulled-back tautological quotient to the tautological quotient, which is
  the property that pins it uniquely (`Stacks.Chow.GenuineChern.existsUnique_twistIso`).

## Why the chosen witness would not do

`AlgebraicGeometry.projectiveBundlePresentationsAgree` is a bare existential with no uniqueness
clause, so a witness drawn from it by `Exists.choose` is an opaque function of the module and no
relation between the witness at `E` and the witness at `E'` is provable. Since an automorphism
of `𝐏(E)` over the base need not carry the universal quotient to the universal quotient, the
datum built from a chosen witness is not even isomorphic *as a datum* to the one built at `E'`,
and the identification below would be false rather than merely unproved. That is why
`Stacks.RelativeProj.bundlePresentationIso` is `Stacks.ProjectiveBundle.presentationIso`.

## Not done here

**That the comparison is an isomorphism of tautological *data*** — the equation

`((tautologicalDatum E).baseChange g E E' hE).univ ≫ (tautologicalDatumTwistBaseChangeIso …).hom
  = (tautologicalDatum E').univ`

— is **proved**, in
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/TautologicalDatumBaseChangeSpec.lean`, as
`Stacks.RelativeProj.tautologicalDatum_baseChange_univ_comp_`
`tautologicalDatumTwistBaseChangeIso_hom`. Tag 0B3V's clause on the universal quotient of the
canonical base-change comparison is read off there, at the canonical datum on both bundles, and
carries the attribute. The description below is
the shape of that proof.

Writing `c` and `c'` for the two presentation comparisons, `h` for
`Stacks.ProjectiveBundle.baseChangeHom`, `S` for
`Stacks.Chow.GenuineChern.twistPullbackSourceIso` and `N` for the composite natural isomorphism
`(pullback c⁻¹ ⋙ pullback b) ≅ (pullback h ⋙ pullback (c')⁻¹)` whose components are the first
three factors of `tautologicalDatumTwistBaseChangeIso`, the equation is equivalent, after
composing with `tautologicalBaseChangeIso` on the left, to three reductions and one residue:

1. the naturality of `N` at `Stacks.ProjectiveBundleSplitting.tautologicalMap E`, which moves
   `b^*(c⁻¹)^*` past it to `(c')^*h^*`;
2. `Stacks.RelativeProj.symTwistBaseChangeIso_spec`, which replaces `h^*(tautologicalMap E)`
   followed by the twist comparison by `S⁻¹` followed by
   `Stacks.Chow.GenuineChern.twistQuotientTarget`;
3. the naturality of `pullbackCongr ∘ pullbackComp` at `hE.inv`, which strips `hE` from both
   sides;

leaving exactly `Stacks.Modules.squarePaste_coherence` at the square
`b ≫ c⁻¹ = (c')⁻¹ ≫ h`, `h ≫ Q = q ≫ g` with the factorizations `c⁻¹ ≫ Q = π` and
`(c')⁻¹ ≫ q = π'`, read with every factor inverted. That residue is the lemma proved above, so
what the companion file adds is the inversion — `Stacks.Modules.squarePaste_flip` — and the three
reductions, not a new coherence.

Two obstacles apply to that bookkeeping:
`rw` and `simp only` do not find `Category.assoc` or `Functor.map_comp` on these composites,
because `(TautologicalDatum.baseChange …).twist` is `(Scheme.Modules.pullback b).obj D.twist`
only after unfolding the structure instance, so the three crossings of that identification must
be made in term mode with `Eq.trans`, `CategoryTheory.whisker_eq` and an explicit
`(Scheme.Modules.pullback g).map_comp`; and an `Iso.trans` of these factors must be decomposed
through named factors with declared types rather than inlined, as
`StacksFrontier/AlgebraicGeometry/InvertibleQuotient/ConormalSource.lean` also records.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SymGraded

universe u

namespace Stacks.Modules

variable {P' P S S' Z Z' : Scheme.{u}}

/-- **The pasting coherence of the pullback pseudofunctor at two commuting squares.** The outer
square `b ≫ π = p ≫ g` is pasted from `b ≫ s = s' ≫ r` and `r ≫ t = q ≫ g` through the two
factorizations `s ≫ t = π` and `s' ≫ q = p`; this says the two resulting identifications of
`b^*π^*M` with `s'^*q^*g^*M` agree. No projective bundle appears: it is
`Stacks.Modules.sectionSquare_coherence` with the two identity morphisms replaced by arbitrary
ones, and like it the proof is three instances of
`Stacks.Modules.pullbackComp_congr_assoc` -- at the triples `(b, s, t)`, `(s', r, t)` and
`(s', q, g)`. The unitality coherences that `sectionSquare_coherence` needs do not appear here,
because no identity does. -/
theorem squarePaste_coherence (b : P' ⟶ P) (s : P ⟶ S) (t : S ⟶ Z) (s' : P' ⟶ S')
    (r : S' ⟶ S) (q : S' ⟶ Z') (g : Z' ⟶ Z) (hb : b ≫ s = s' ≫ r) (hr : r ≫ t = q ≫ g)
    (π : P ⟶ Z) (hs : s ≫ t = π) (p : P' ⟶ Z') (hq : s' ≫ q = p)
    (hbp : b ≫ π = p ≫ g) (M : Z.Modules) :
    (Scheme.Modules.pullback b).map ((Scheme.Modules.pullbackComp s t).hom.app M) ≫
        (Scheme.Modules.pullback b).map ((Scheme.Modules.pullbackCongr hs).hom.app M) ≫
        (Scheme.Modules.pullbackComp b π).hom.app M ≫
        (Scheme.Modules.pullbackCongr hbp).hom.app M =
      (Scheme.Modules.pullbackComp b s).hom.app ((Scheme.Modules.pullback t).obj M) ≫
        (Scheme.Modules.pullbackCongr hb).hom.app ((Scheme.Modules.pullback t).obj M) ≫
        (Scheme.Modules.pullbackComp s' r).inv.app ((Scheme.Modules.pullback t).obj M) ≫
        (Scheme.Modules.pullback s').map ((Scheme.Modules.pullbackComp r t).hom.app M) ≫
        (Scheme.Modules.pullback s').map ((Scheme.Modules.pullbackCongr hr).hom.app M) ≫
        (Scheme.Modules.pullback s').map ((Scheme.Modules.pullbackComp q g).inv.app M) ≫
        (Scheme.Modules.pullbackComp s' q).hom.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackCongr hq).hom.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackComp p g).hom.app M := by
  have he : (s' ≫ r) ≫ t = p ≫ g := by
    rw [Category.assoc, hr, ← Category.assoc, hq]
  have h1 := pullbackComp_congr_assoc b s t (s' ≫ r) hb π hs (p ≫ g) he M
  have h2 := pullbackComp_congr_assoc s' r t (s' ≫ r) rfl (q ≫ g) hr (p ≫ g) he M
  have h3 := pullbackComp_congr_assoc s' q g p hq (q ≫ g) rfl (p ≫ g) rfl M
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app, eqToHom_refl,
    NatTrans.id_app, Category.comp_id, Functor.map_comp, Category.assoc] at h1 h2 h3 ⊢
  rw [h1]
  refine whisker_eq _ (whisker_eq _ ?_)
  rw [← h3]
  have hcancel : (Scheme.Modules.pullback s').map ((Scheme.Modules.pullbackComp q g).inv.app M) ≫
      (Scheme.Modules.pullback s').map ((Scheme.Modules.pullbackComp q g).hom.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, (Scheme.Modules.pullback s').map_id]
  rw [reassoc_of% hcancel, h2, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

end Stacks.Modules

namespace Stacks.RelativeProj

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent]
  (E' : X'.Modules) [E'.IsQuasicoherent] (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- **The base-change square of the two presentations**: the base-change morphism of
`Stacks.RelativeProj.projectiveBundle`, followed by the inverse presentation comparison at `E`,
is the inverse presentation comparison at `E'` followed by the base-change morphism of the
`SheafGradedAlgebra` substrate. Immediate from the definition of
`Stacks.ProjectiveBundle.baseChangeHom`. -/
@[reassoc] theorem projectiveBundleBaseChange_comp_bundlePresentationIso_inv :
    projectiveBundleBaseChange g E E' hE ≫ (bundlePresentationIso E).inv =
      (bundlePresentationIso E').inv ≫
        Stacks.ProjectiveBundle.baseChangeHom g E (isQuasicoherentPieces_of_isQuasicoherent E)
          E' (isQuasicoherentPieces_of_isQuasicoherent E') hE := by
  show projectiveBundleBaseChange g E E' hE ≫
      (Stacks.ProjectiveBundle.presentationIso E
        (isQuasicoherentPieces_of_isQuasicoherent E)).inv =
    (Stacks.ProjectiveBundle.presentationIso E'
        (isQuasicoherentPieces_of_isQuasicoherent E')).inv ≫
      Stacks.ProjectiveBundle.baseChangeHom g E (isQuasicoherentPieces_of_isQuasicoherent E)
        E' (isQuasicoherentPieces_of_isQuasicoherent E') hE
  rw [Stacks.ProjectiveBundle.baseChangeHom, Iso.inv_hom_id_assoc]

/-- **The comparison of the tautological twists on the `SheafGradedAlgebra` substrate**,
`h^*𝒪(1) ≅ 𝒪(1)` for `h` the base-change morphism of that substrate. This is
`Stacks.Chow.GenuineChern.twistPullbackIso` at `u = hE⁻¹`, whose chart hypothesis is discharged
by `Stacks.ProjectiveBundle.exists_chart_baseChangeHom`; so it is unconditional in `g`, `E` and
`E'`, and by `Stacks.Chow.GenuineChern.existsUnique_twistIso` it is the only isomorphism with
the property recorded in `Stacks.RelativeProj.symTwistBaseChangeIso_spec`. -/
@[ega "II 4.1.3" "(1), special case"]
def symTwistBaseChangeIso :
    (Scheme.Modules.pullback
          (Stacks.ProjectiveBundle.baseChangeHom g E
            (isQuasicoherentPieces_of_isQuasicoherent E) E'
            (isQuasicoherentPieces_of_isQuasicoherent E') hE)).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
          (isQuasicoherentPieces_of_isQuasicoherent E)) ≅
      Stacks.ProjectiveBundleSplitting.tautologicalTwist E'
        (isQuasicoherentPieces_of_isQuasicoherent E') :=
  Stacks.Chow.GenuineChern.twistPullbackIso g (isQuasicoherentPieces_of_isQuasicoherent E)
    (isQuasicoherentPieces_of_isQuasicoherent E') hE.inv _
    (Stacks.ProjectiveBundle.baseChangeHom_toBase g E
      (isQuasicoherentPieces_of_isQuasicoherent E) E'
      (isQuasicoherentPieces_of_isQuasicoherent E') hE)
    (Stacks.ProjectiveBundle.exists_chart_baseChangeHom g E
      (isQuasicoherentPieces_of_isQuasicoherent E) E'
      (isQuasicoherentPieces_of_isQuasicoherent E') hE)

/-- **The comparison of the tautological twists is pinned**: it carries the pulled-back
tautological quotient of `E` to the tautological quotient of `E'` read through `hE`. By
`Stacks.Chow.GenuineChern.existsUnique_twistIso` it is the only isomorphism that does. -/
@[reassoc] theorem symTwistBaseChangeIso_spec :
    Stacks.Chow.GenuineChern.twistQuotientPullback g
          (isQuasicoherentPieces_of_isQuasicoherent E)
          (isQuasicoherentPieces_of_isQuasicoherent E') _
          (Stacks.ProjectiveBundle.baseChangeHom_toBase g E
            (isQuasicoherentPieces_of_isQuasicoherent E) E'
            (isQuasicoherentPieces_of_isQuasicoherent E') hE) ≫
        (symTwistBaseChangeIso g E E' hE).hom =
      Stacks.Chow.GenuineChern.twistQuotientTarget g
        (isQuasicoherentPieces_of_isQuasicoherent E') hE.inv :=
  Stacks.Chow.GenuineChern.twistQuotientPullback_comp_twistPullbackIso g _ _ hE.inv _ _ _

/-- **The comparison of the tautological twists on `Stacks.RelativeProj.projectiveBundle`**:
`b^*𝒪_{𝐏(E)}(1) ≅ 𝒪_{𝐏(E')}(1)`, unconditionally in `g`, `E` and `E'`. The two presentation
comparisons carry `b` to the base-change morphism of the `SheafGradedAlgebra` substrate, by
`Stacks.RelativeProj.projectiveBundleBaseChange_comp_bundlePresentationIso_inv`, and the
comparison of the twists there is `Stacks.RelativeProj.symTwistBaseChangeIso`. -/
@[ega "II 4.1.3" "(1), special case"]
def tautologicalDatumTwistBaseChangeIso :
    (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).obj
        (tautologicalDatumTwist E) ≅ tautologicalDatumTwist E' :=
  (Scheme.Modules.pullbackComp (projectiveBundleBaseChange g E E' hE)
        (bundlePresentationIso E).inv).app
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
        (isQuasicoherentPieces_of_isQuasicoherent E)) ≪≫
    (Scheme.Modules.pullbackCongr
        (projectiveBundleBaseChange_comp_bundlePresentationIso_inv g E E' hE)).app
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
        (isQuasicoherentPieces_of_isQuasicoherent E)) ≪≫
    ((Scheme.Modules.pullbackComp (bundlePresentationIso E').inv
        (Stacks.ProjectiveBundle.baseChangeHom g E
          (isQuasicoherentPieces_of_isQuasicoherent E) E'
          (isQuasicoherentPieces_of_isQuasicoherent E') hE)).app
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
        (isQuasicoherentPieces_of_isQuasicoherent E))).symm ≪≫
    (Scheme.Modules.pullback (bundlePresentationIso E').inv).mapIso
      (symTwistBaseChangeIso g E E' hE)

end Stacks.RelativeProj

end
