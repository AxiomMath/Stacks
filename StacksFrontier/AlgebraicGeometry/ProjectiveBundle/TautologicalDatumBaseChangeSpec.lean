module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChange

/-!
# The canonical base-change comparison carries the universal quotient to the universal quotient

Let `g : X' ⟶ X` be a morphism of schemes, `E` a quasi-coherent `𝒪_X`-module, `E'` a
quasi-coherent `𝒪_{X'}`-module and `hE : E' ≅ g^*E`. Write `π : 𝐏(E) ⟶ X` and `π' : 𝐏(E') ⟶ X'`
for the two projections and `b : 𝐏(E') ⟶ 𝐏(E)` for the base-change comparison
`Stacks.RelativeProj.projectiveBundleBaseChange`.

For the canonical tautological data `Stacks.RelativeProj.tautologicalDatum` of `𝐏(E)` and
`𝐏(E')`, this file shows that the comparison
`Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso` of their twists carries the pullback
along `b` of the universal quotient `π^*E ⟶ 𝒪_{𝐏(E)}(1)` to the universal quotient
`π'^*E' ⟶ 𝒪_{𝐏(E')}(1)`, read through the canonical identification of `b^*π^*E` with
`π'^*E'`. Equivalently, the base change along `b` of the canonical datum of
`𝐏(E)` is the canonical datum of `𝐏(E')`.

## Main results

* `Stacks.Modules.tautologicalBaseChange_general`: the identity at arbitrary schemes: for `b`,
  two presentation comparisons `k`, `k'`, a morphism `hh` between the second presentations and
  two tautological quotients `t`, `t'` whose targets are identified by an isomorphism `sym`
  compatible with the pulled-back module, the transport of `t` along `b` is `t'`.
* `Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso_spec`: that identity at the
  projective bundle, and `Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso_spec'` with the
  comparison of `b^*π^*E` with `π'^*E'` written as `Stacks.RelativeProj.tautologicalBaseChangeIso`.
* `RelativeProj.tautologicalDatum_baseChange_univ_comp_tautologicalDatumTwistBaseChangeIso_hom`:
  the base change of the canonical datum is the canonical datum.
* `Stacks.RelativeProj.projectiveBundleBaseChangeIsoFlip_tautological_canonical`: the same
  statement for the second projection of the comparison isomorphism `𝐏(E') ≅ X' ×_X 𝐏(E)`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/


@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SymGraded
universe u

namespace Stacks.Modules

variable {P P' R R' B B' : Scheme.{u}}

/-- The forward map of `pullbackCongr h.symm` is the inverse of `pullbackCongr h`. -/
theorem pullbackCongr_symm_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (Scheme.Modules.pullbackCongr h.symm).hom = (Scheme.Modules.pullbackCongr h).inv := by
  subst h; rfl

/-- The inverse of `pullbackCongr h.symm` is the forward map of `pullbackCongr h`. -/
theorem pullbackCongr_symm_inv {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (Scheme.Modules.pullbackCongr h.symm).inv = (Scheme.Modules.pullbackCongr h).hom := by
  subst h; rfl

/-- Naturality of the three-factor square comparison. -/
theorem squareComp_naturality (b : P' ⟶ P) (k : P ⟶ R) (k' : P' ⟶ R') (hh : R' ⟶ R)
    (hbk : b ≫ k = k' ≫ hh) {M N : R.Modules} (f : M ⟶ N) :
    (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback k).map f) ≫
        (Scheme.Modules.pullbackComp b k).hom.app N ≫
        (Scheme.Modules.pullbackCongr hbk).hom.app N ≫
        (Scheme.Modules.pullbackComp k' hh).inv.app N =
      (Scheme.Modules.pullbackComp b k).hom.app M ≫
        (Scheme.Modules.pullbackCongr hbk).hom.app M ≫
        (Scheme.Modules.pullbackComp k' hh).inv.app M ≫
        (Scheme.Modules.pullback k').map ((Scheme.Modules.pullback hh).map f) := by
  simpa using ((Scheme.Modules.pullbackComp b k).hom ≫ (Scheme.Modules.pullbackCongr hbk).hom ≫
    (Scheme.Modules.pullbackComp k' hh).inv).naturality f

/-- Naturality of the two-factor factorisation comparison, inverse side. -/
theorem congrComp_inv_naturality (k' : P' ⟶ R') (q : R' ⟶ B') (p : P' ⟶ B')
    (hq : k' ≫ q = p) {M N : B'.Modules} (f : M ⟶ N) :
    (Scheme.Modules.pullbackCongr hq).inv.app M ≫
        (Scheme.Modules.pullbackComp k' q).inv.app M ≫
        (Scheme.Modules.pullback k').map ((Scheme.Modules.pullback q).map f) =
      (Scheme.Modules.pullback p).map f ≫
        (Scheme.Modules.pullbackCongr hq).inv.app N ≫
        (Scheme.Modules.pullbackComp k' q).inv.app N := by
  simp

/-- Associativity of a four-fold composite against a fifth factor, in a bare category. -/
theorem comp_assoc_right {C : Type*} [Category C] {A B₁ B₂ B₃ B₄ B₅ : C}
    (a : A ⟶ B₁) (b : B₁ ⟶ B₂) (c : B₂ ⟶ B₃) (d : B₃ ⟶ B₄) (u : B₄ ⟶ B₅) :
    (a ≫ b ≫ c ≫ d) ≫ u = a ≫ b ≫ c ≫ d ≫ u := by
  simp

/-- A bare-category rearrangement of a pasting identity. -/
theorem flip_paste {C : Type*} [Category C] {A B₁ B₂ B₃ B₄ : C}
    (φ : B₁ ≅ A) (c : A ≅ B₂) (n : B₁ ≅ B₃) (w : B₄ ≅ B₃) (d : B₄ ≅ B₂)
    (H : φ.hom ≫ c.hom = n.hom ≫ w.inv ≫ d.hom) :
    c.hom ≫ d.inv ≫ w.hom = φ.inv ≫ n.hom := by
  rw [← cancel_epi φ.hom, reassoc_of% H]
  simp

/-- The pasting coherence, rearranged so that the right-hand side crosses no comparison
backwards. -/
theorem squarePaste_flip (b : P' ⟶ P) (k : P ⟶ R) (Q : R ⟶ B) (k' : P' ⟶ R')
    (hh : R' ⟶ R) (q : R' ⟶ B') (g : B' ⟶ B) (hbk : b ≫ k = k' ≫ hh)
    (hhQ : hh ≫ Q = q ≫ g) (π : P ⟶ B) (hk : k ≫ Q = π) (π' : P' ⟶ B')
    (hk' : k' ≫ q = π') (hb : b ≫ π = π' ≫ g) (M : B.Modules) :
    (Scheme.Modules.pullbackComp b π).hom.app M ≫
        (Scheme.Modules.pullbackCongr hb).hom.app M ≫
        (Scheme.Modules.pullbackComp π' g).inv.app M ≫
        (Scheme.Modules.pullbackCongr hk').inv.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackComp k' q).inv.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullback k').map ((Scheme.Modules.pullbackComp q g).hom.app M) ≫
        (Scheme.Modules.pullback k').map
          ((Scheme.Modules.pullbackCongr hhQ.symm).hom.app M) ≫
        (Scheme.Modules.pullback k').map ((Scheme.Modules.pullbackComp hh Q).inv.app M) =
      (Scheme.Modules.pullback b).map ((Scheme.Modules.pullbackCongr hk).inv.app M) ≫
        (Scheme.Modules.pullback b).map ((Scheme.Modules.pullbackComp k Q).inv.app M) ≫
        (Scheme.Modules.pullbackComp b k).hom.app ((Scheme.Modules.pullback Q).obj M) ≫
        (Scheme.Modules.pullbackCongr hbk).hom.app ((Scheme.Modules.pullback Q).obj M) ≫
        (Scheme.Modules.pullbackComp k' hh).inv.app ((Scheme.Modules.pullback Q).obj M) := by
  have hcs : (Scheme.Modules.pullbackCongr hhQ.symm).inv =
      (Scheme.Modules.pullbackCongr hhQ).hom := pullbackCongr_symm_inv hhQ
  have key := flip_paste
    ((Scheme.Modules.pullback b).mapIso
      ((Scheme.Modules.pullbackComp k Q).app M ≪≫ (Scheme.Modules.pullbackCongr hk).app M))
    ((Scheme.Modules.pullbackComp b π).app M ≪≫ (Scheme.Modules.pullbackCongr hb).app M)
    ((Scheme.Modules.pullbackComp b k).app ((Scheme.Modules.pullback Q).obj M) ≪≫
      (Scheme.Modules.pullbackCongr hbk).app ((Scheme.Modules.pullback Q).obj M) ≪≫
      ((Scheme.Modules.pullbackComp k' hh).app ((Scheme.Modules.pullback Q).obj M)).symm)
    ((Scheme.Modules.pullback k').mapIso
      ((Scheme.Modules.pullbackComp q g).app M ≪≫
        (Scheme.Modules.pullbackCongr hhQ.symm).app M ≪≫
        ((Scheme.Modules.pullbackComp hh Q).app M).symm))
    ((Scheme.Modules.pullbackComp k' q).app ((Scheme.Modules.pullback g).obj M) ≪≫
      (Scheme.Modules.pullbackCongr hk').app ((Scheme.Modules.pullback g).obj M) ≪≫
      (Scheme.Modules.pullbackComp π' g).app M)
    (by
      simpa [hcs] using
        squarePaste_coherence b k Q k' hh q g hbk hhQ π hk π' hk' hb M)
  simpa using key

/-- `b` compares two relative `Proj`s, `k` and `k'` compare the two presentations of each, `hh` is
the base-change morphism on the second presentation, `t` and `t'` are the two tautological
quotients and `sym` the comparison of their targets, pinned by `hsym`. The conclusion is that
the transported tautological quotient of `M` is the tautological quotient of `M'`. -/
theorem tautologicalBaseChange_general
    (b : P' ⟶ P) (k : P ⟶ R) (k' : P' ⟶ R') (hh : R' ⟶ R)
    (Q : R ⟶ B) (q : R' ⟶ B') (g : B' ⟶ B) (π : P ⟶ B) (π' : P' ⟶ B')
    (hk : k ≫ Q = π) (hk' : k' ≫ q = π') (hbk : b ≫ k = k' ≫ hh)
    (hhQ : hh ≫ Q = q ≫ g) (hb : b ≫ π = π' ≫ g)
    {M : B.Modules} {M' : B'.Modules} (e : (Scheme.Modules.pullback g).obj M ⟶ M')
    {T : R.Modules} {T' : R'.Modules}
    (t : (Scheme.Modules.pullback Q).obj M ⟶ T)
    (t' : (Scheme.Modules.pullback q).obj M' ⟶ T')
    (sym : (Scheme.Modules.pullback hh).obj T ≅ T')
    (hsym :
      (((Scheme.Modules.pullbackComp q g).hom.app M ≫
            (Scheme.Modules.pullbackCongr hhQ.symm).hom.app M ≫
            (Scheme.Modules.pullbackComp hh Q).inv.app M) ≫
          (Scheme.Modules.pullback hh).map t) ≫ sym.hom =
      (Scheme.Modules.pullback q).map e ≫ t') :
    (Scheme.Modules.pullback b).map
          ((Scheme.Modules.pullbackCongr hk).inv.app M ≫
            (Scheme.Modules.pullbackComp k Q).inv.app M ≫
            (Scheme.Modules.pullback k).map t) ≫
        (Scheme.Modules.pullbackComp b k).hom.app T ≫
        (Scheme.Modules.pullbackCongr hbk).hom.app T ≫
        (Scheme.Modules.pullbackComp k' hh).inv.app T ≫
        (Scheme.Modules.pullback k').map sym.hom =
      (Scheme.Modules.pullbackComp b π).hom.app M ≫
        (Scheme.Modules.pullbackCongr hb).hom.app M ≫
        (Scheme.Modules.pullbackComp π' g).inv.app M ≫
        (Scheme.Modules.pullback π').map e ≫
        (Scheme.Modules.pullbackCongr hk').inv.app M' ≫
        (Scheme.Modules.pullbackComp k' q).inv.app M' ≫
        (Scheme.Modules.pullback k').map t' := by
  simp only [Category.assoc] at hsym
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    reassoc_of% (squareComp_naturality b k k' hh hbk t),
    ← reassoc_of% (squarePaste_flip b k Q k' hh q g hbk hhQ π hk π' hk' hb M),
    ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, hsym,
    Functor.map_comp, reassoc_of% (congrComp_inv_naturality k' q π' hk' e)]

end Stacks.Modules

namespace Stacks.RelativeProj

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent]
  (E' : X'.Modules) [E'.IsQuasicoherent] (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- The tautological surjection of `𝐏(F)`, as the composite it is defined to be. -/
theorem tautologicalDatumUniv_eq {Z : Scheme.{u}} (F : Z.Modules) [F.IsQuasicoherent] :
    tautologicalDatumUniv F =
      (Scheme.Modules.pullbackCongr (bundlePresentationIso_inv_comp_toBase F)).inv.app F ≫
        (Scheme.Modules.pullbackComp (bundlePresentationIso F).inv
          (symGradedBundle F).toBase).inv.app F ≫
        (Scheme.Modules.pullback (bundlePresentationIso F).inv).map
          (Stacks.ProjectiveBundleSplitting.tautologicalMap F
            (isQuasicoherentPieces_of_isQuasicoherent F)) :=
  rfl

/-- The comparison of the tautological twists, as the composite it is defined to be. -/
theorem tautologicalDatumTwistBaseChangeIso_hom :
    (tautologicalDatumTwistBaseChangeIso g E E' hE).hom =
      (Scheme.Modules.pullbackComp (projectiveBundleBaseChange g E E' hE)
            (bundlePresentationIso E).inv).hom.app
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
            (isQuasicoherentPieces_of_isQuasicoherent E)) ≫
        (Scheme.Modules.pullbackCongr
            (projectiveBundleBaseChange_comp_bundlePresentationIso_inv g E E' hE)).hom.app
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
            (isQuasicoherentPieces_of_isQuasicoherent E)) ≫
        (Scheme.Modules.pullbackComp (bundlePresentationIso E').inv
            (Stacks.ProjectiveBundle.baseChangeHom g E
              (isQuasicoherentPieces_of_isQuasicoherent E) E'
              (isQuasicoherentPieces_of_isQuasicoherent E') hE)).inv.app
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
            (isQuasicoherentPieces_of_isQuasicoherent E)) ≫
        (Scheme.Modules.pullback (bundlePresentationIso E').inv).map
          (symTwistBaseChangeIso g E E' hE).hom :=
  rfl

/-- The comparison of the tautological twists is an isomorphism of tautological quotients: the
pullback along the canonical base-change comparison of `𝐏(E)`'s own universal quotient is
`𝐏(E')`'s own universal quotient, read through the canonical identification of `b^*π^*E` with
`π'^*E'`. -/
theorem tautologicalDatumTwistBaseChangeIso_spec :
    (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).map
          (tautologicalDatumUniv E) ≫
        (tautologicalDatumTwistBaseChangeIso g E E' hE).hom =
      (Scheme.Modules.pullbackComp (projectiveBundleBaseChange g E E' hE)
          (projectiveBundleToBase X E)).hom.app E ≫
        (Scheme.Modules.pullbackCongr
          (projectiveBundleBaseChange_comp_projectiveBundleToBase g E E' hE)).hom.app E ≫
        (Scheme.Modules.pullbackComp (projectiveBundleToBase X' E') g).inv.app E ≫
        (Scheme.Modules.pullback (projectiveBundleToBase X' E')).map hE.inv ≫
        tautologicalDatumUniv E'   := by
  have h :=
    Stacks.Modules.tautologicalBaseChange_general
      (projectiveBundleBaseChange g E E' hE) (bundlePresentationIso E).inv
      (bundlePresentationIso E').inv
      (Stacks.ProjectiveBundle.baseChangeHom g E (isQuasicoherentPieces_of_isQuasicoherent E) E'
        (isQuasicoherentPieces_of_isQuasicoherent E') hE)
      (symGradedBundle E).toBase (symGradedBundle E').toBase g
      (projectiveBundleToBase X E) (projectiveBundleToBase X' E')
      (bundlePresentationIso_inv_comp_toBase E) (bundlePresentationIso_inv_comp_toBase E')
      (projectiveBundleBaseChange_comp_bundlePresentationIso_inv g E E' hE)
      (Stacks.ProjectiveBundle.baseChangeHom_toBase g E
        (isQuasicoherentPieces_of_isQuasicoherent E) E'
        (isQuasicoherentPieces_of_isQuasicoherent E') hE)
      (projectiveBundleBaseChange_comp_projectiveBundleToBase g E E' hE) hE.inv
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E
        (isQuasicoherentPieces_of_isQuasicoherent E))
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E'
        (isQuasicoherentPieces_of_isQuasicoherent E'))
      (symTwistBaseChangeIso g E E' hE) (symTwistBaseChangeIso_spec g E E' hE)
  rw [tautologicalDatumUniv_eq E, tautologicalDatumTwistBaseChangeIso_hom g E E' hE,
    tautologicalDatumUniv_eq E']
  exact h

/-- The same identity with the four-step comparison written as
`Stacks.RelativeProj.tautologicalBaseChangeIso`. -/
theorem tautologicalDatumTwistBaseChangeIso_spec' :
    (Scheme.Modules.pullback (projectiveBundleBaseChange g E E' hE)).map
          (tautologicalDatumUniv E) ≫
        (tautologicalDatumTwistBaseChangeIso g E E' hE).hom =
      (tautologicalBaseChangeIso g E E' hE).hom ≫ tautologicalDatumUniv E' :=
  (tautologicalDatumTwistBaseChangeIso_spec g E E' hE).trans
    (((congrArg (fun z => z ≫ tautologicalDatumUniv E')
          (tautologicalBaseChangeIso_hom g E E' hE)).trans
        (Stacks.Modules.comp_assoc_right _ _ _ _ _)).symm)

/-- The base change of the canonical tautological datum is the canonical tautological datum: the
universal surjection of the base-changed datum, composed with the comparison of the twists, is
`𝐏(E')`'s own universal surjection. -/
theorem tautologicalDatum_baseChange_univ_comp_tautologicalDatumTwistBaseChangeIso_hom :
    ((tautologicalDatum E).baseChange g E E' hE).univ ≫
        (tautologicalDatumTwistBaseChangeIso g E E' hE).hom =
      (tautologicalDatum E').univ :=
  ((Category.assoc _ _ _).trans
    ((congrArg (fun w => (tautologicalBaseChangeIso g E E' hE).inv ≫ w)
        (tautologicalDatumTwistBaseChangeIso_spec' g E E' hE)).trans
      (Iso.inv_hom_id_assoc _ _)))

/-- For a morphism `b` equal to the canonical base-change comparison, the pullback along `b` of
the universal quotient of `𝐏(E)` is, up to an isomorphism of twists, the universal quotient of
`𝐏(E')`. -/
theorem projectiveBundleBaseChange_tautological_canonical_of_eq
    (b : projectiveBundle X' E' ⟶ projectiveBundle X E)
    (hb0 : projectiveBundleBaseChange g E E' hE = b)
    (hb : b ≫ projectiveBundleToBase X E = projectiveBundleToBase X' E' ≫ g) :
    ∃ α : (Scheme.Modules.pullback b).obj (tautologicalDatumTwist E) ≅
        tautologicalDatumTwist E',
      (Scheme.Modules.pullback b).map (tautologicalDatumUniv E) ≫ α.hom =
        (Scheme.Modules.pullbackComp b (projectiveBundleToBase X E)).hom.app E ≫
          (Scheme.Modules.pullbackCongr hb).hom.app E ≫
          (Scheme.Modules.pullbackComp (projectiveBundleToBase X' E') g).inv.app E ≫
          (Scheme.Modules.pullback (projectiveBundleToBase X' E')).map hE.inv ≫
          tautologicalDatumUniv E' := by
  subst hb0
  exact ⟨tautologicalDatumTwistBaseChangeIso g E E' hE,
    tautologicalDatumTwistBaseChangeIso_spec g E E' hE⟩

/-- The second projection `b : 𝐏(E') ⟶ 𝐏(E)` of the comparison isomorphism
`𝐏(E') ≅ X' ×_X 𝐏(E)` carries the universal quotient of `𝐏(E)` to the universal quotient of
`𝐏(E')`, up to an isomorphism of twists. -/
theorem projectiveBundleBaseChangeIsoFlip_tautological_canonical :
    ∃ α : (Scheme.Modules.pullback ((projectiveBundleBaseChangeIsoFlip g E E' hE).hom ≫
          pullback.snd g (projectiveBundleToBase X E))).obj (tautologicalDatumTwist E) ≅
        tautologicalDatumTwist E',
      (Scheme.Modules.pullback ((projectiveBundleBaseChangeIsoFlip g E E' hE).hom ≫
            pullback.snd g (projectiveBundleToBase X E))).map (tautologicalDatumUniv E) ≫
          α.hom =
        (Scheme.Modules.pullbackComp ((projectiveBundleBaseChangeIsoFlip g E E' hE).hom ≫
              pullback.snd g (projectiveBundleToBase X E))
            (projectiveBundleToBase X E)).hom.app E ≫
          (Scheme.Modules.pullbackCongr
            (projectiveBundleBaseChangeIsoFlip_hom_snd_comp_projectiveBundleToBase
              g E E' hE)).hom.app E ≫
          (Scheme.Modules.pullbackComp (projectiveBundleToBase X' E') g).inv.app E ≫
          (Scheme.Modules.pullback (projectiveBundleToBase X' E')).map hE.inv ≫
          tautologicalDatumUniv E' :=
  projectiveBundleBaseChange_tautological_canonical_of_eq g E E' hE _
    (projectiveBundleBaseChangeIsoFlip_hom_snd g E E' hE).symm
    (projectiveBundleBaseChangeIsoFlip_hom_snd_comp_projectiveBundleToBase g E E' hE)

end Stacks.RelativeProj
end
