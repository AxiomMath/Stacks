module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SubbundleTwist
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChangeSpec

/-!
# The twist of `𝐏(𝒢)` restricted to `𝐏(𝒬)`, in the `Situation` presentation

Let `X` be a scheme and `g : 𝒢 ⟶ 𝒬` a surjection of finite locally free `𝒪_X`-modules. The
closed immersion `ι : 𝐏(𝒬) ⟶ 𝐏(𝒢)` pulls the twist `𝒪_{𝐏(𝒢)}(1)` back to `𝒪_{𝐏(𝒬)}(1)`,
carrying the pulled-back tautological quotient `ι^*π_𝒢^*𝒢 ⟶ ι^*𝒪_{𝐏(𝒢)}(1)` to the tautological
quotient of `𝒬` precomposed with `π_𝒬^*g`. For the `SheafGradedAlgebra` presentation of the
projective bundles this is
`Stacks.Chow.GenuineChern.twistQuotientPullback_comp_bundleEmbeddingTwistIso`;
this file carries it over to the presentation `Stacks.RelativeProj.projectiveBundle` with its
tautological datum `Stacks.RelativeProj.tautologicalDatumUniv`, through the comparison
isomorphisms `Stacks.RelativeProj.bundlePresentationIso`.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.situationEmbedding`: the closed immersion
  `𝐏(𝒬) ⟶ 𝐏(𝒢)` of `Stacks.RelativeProj.projectiveBundle`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.situationEmbedding_comp_toBase`: it lies over `X`.
* `AlgebraicGeometry.Space.PrivateChern.exists_situationEmbedding_twistIso`: an isomorphism
  `ι^*𝒪_{𝐏(𝒢)}(1) ≅ 𝒪_{𝐏(𝒬)}(1)` carrying the pulled-back tautological quotient of `𝒢` to the
  tautological quotient of `𝒬` precomposed with `g`.

## Implementation notes

The comparison is obtained from an identity between composites of the canonical isomorphisms
`(f ≫ g)^* ≅ f^* ⋙ g^*` and `f^* ≅ f'^*` (for `f = f'`) at arbitrary schemes and morphisms
(`Stacks.Modules.tautologicalBaseChange_general`), instantiated once; the identification of the
two pullbacks of `𝒢` enters as a named isomorphism with its defining equation, so the composite
is never re-associated inside the concrete projective bundles.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [-instance] CategoryTheory.catToReflQuiver

section General


variable {P P' R R' B B' : Scheme.{u}}

/-- `Stacks.Modules.tautologicalBaseChange_general` with the identification of the two pullbacks
of `M` written as a composite of isomorphisms, the form of
`Stacks.Chow.GenuineChern.twistPullbackSourceIso`. -/
private theorem tautologicalBaseChange_general_iso
    (b : P' ⟶ P) (k : P ⟶ R) (k' : P' ⟶ R') (hh : R' ⟶ R)
    (Q : R ⟶ B) (q : R' ⟶ B') (g : B' ⟶ B) (π : P ⟶ B) (π' : P' ⟶ B')
    (hk : k ≫ Q = π) (hk' : k' ≫ q = π') (hbk : b ≫ k = k' ≫ hh)
    (hhQ : hh ≫ Q = q ≫ g) (hb : b ≫ π = π' ≫ g)
    {M : B.Modules} {M' : B'.Modules} (e : (Scheme.Modules.pullback g).obj M ⟶ M')
    {T : R.Modules} {T' : R'.Modules}
    (t : (Scheme.Modules.pullback Q).obj M ⟶ T)
    (t' : (Scheme.Modules.pullback q).obj M' ⟶ T')
    (sym : (Scheme.Modules.pullback hh).obj T ≅ T')
    (src : (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj M) ≅
      (Scheme.Modules.pullback hh).obj ((Scheme.Modules.pullback Q).obj M))
    (hsrc : src = (Scheme.Modules.pullbackComp q g).app M ≪≫
      (Scheme.Modules.pullbackCongr hhQ.symm).app M ≪≫
        ((Scheme.Modules.pullbackComp hh Q).app M).symm)
    (hsym : (src.hom ≫ (Scheme.Modules.pullback hh).map t) ≫ sym.hom =
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
        (Scheme.Modules.pullback k').map t' :=
  Stacks.Modules.tautologicalBaseChange_general b k k' hh Q q g π π' hk hk' hbk hhQ hb e t t' sym
    (by subst hsrc; simpa only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv] using hsym)

/-- Left unitality of the pullback pseudofunctor, read at a module and composed with
`pullbackCongr`. -/
private theorem pullbackCongr_comp_pullbackComp_id_inv {P B : Scheme.{u}} {π π' : P ⟶ B}
    (hb : π = π' ≫ 𝟙 B) (hb' : π = π') (M M' : B.Modules) (e : M ⟶ M') :
    (Scheme.Modules.pullbackCongr hb).hom.app M ≫
        (Scheme.Modules.pullbackComp π' (𝟙 B)).inv.app M ≫
        (Scheme.Modules.pullback π').map ((Scheme.Modules.pullbackId B).hom.app M ≫ e) =
      (Scheme.Modules.pullbackCongr hb').hom.app M ≫ (Scheme.Modules.pullback π').map e := by
  subst hb'
  have hu := congrArg (fun α => α.app M)
    (Scheme.Modules.pseudofunctor_left_unitality (X := P) (Y := B) π)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    eqToHom_app] at hu
  have hu' : (Scheme.Modules.pullbackComp π (𝟙 B)).inv.app M ≫
      (Scheme.Modules.pullback π).map ((Scheme.Modules.pullbackId B).hom.app M) =
        eqToHom (by simp) :=
    (congrArg ((Scheme.Modules.pullbackComp π (𝟙 B)).inv.app M ≫ ·)
      (Category.comp_id ((Scheme.Modules.pullback π).map
        ((Scheme.Modules.pullbackId B).hom.app M)))).symm.trans hu
  rw [Functor.map_comp, ← Category.assoc ((Scheme.Modules.pullbackComp π (𝟙 B)).inv.app M), hu']
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, NatTrans.id_app]

/-- **The twist comparison of two presentations, existence form.** In the situation of
`Stacks.Modules.tautologicalBaseChange_general` over `g = 𝟙`, an isomorphism `sym` of the twists of
the second presentation, compatible with the tautological quotients, gives one of the first
presentation compatible with the transported tautological quotients. -/
private theorem exists_iso_of_tautologicalBaseChange
    (b : P' ⟶ P) (k : P ⟶ R) (k' : P' ⟶ R') (hh : R' ⟶ R)
    (Q : R ⟶ B) (q : R' ⟶ B) (π : P ⟶ B) (π' : P' ⟶ B)
    (hk : k ≫ Q = π) (hk' : k' ≫ q = π') (hbk : b ≫ k = k' ≫ hh)
    (hhQ : hh ≫ Q = q ≫ 𝟙 B) (hb : b ≫ π = π')
    {M M' : B.Modules} (e : M ⟶ M') {T : R.Modules} {T' : R'.Modules}
    (t : (Scheme.Modules.pullback Q).obj M ⟶ T)
    (t' : (Scheme.Modules.pullback q).obj M' ⟶ T')
    (sym : (Scheme.Modules.pullback hh).obj T ≅ T')
    (src : (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback (𝟙 B)).obj M) ≅
      (Scheme.Modules.pullback hh).obj ((Scheme.Modules.pullback Q).obj M))
    (hsrc : src = (Scheme.Modules.pullbackComp q (𝟙 B)).app M ≪≫
      (Scheme.Modules.pullbackCongr hhQ.symm).app M ≪≫
        ((Scheme.Modules.pullbackComp hh Q).app M).symm)
    (hsym : (src.hom ≫ (Scheme.Modules.pullback hh).map t) ≫ sym.hom =
      (Scheme.Modules.pullback q).map ((Scheme.Modules.pullbackId B).hom.app M ≫ e) ≫ t') :
    ∃ θ : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback k).obj T) ≅
        (Scheme.Modules.pullback k').obj T',
      (Scheme.Modules.pullback b).map
          ((Scheme.Modules.pullbackCongr hk).inv.app M ≫
            (Scheme.Modules.pullbackComp k Q).inv.app M ≫
            (Scheme.Modules.pullback k).map t) ≫ θ.hom =
        (Scheme.Modules.pullbackComp b π).hom.app M ≫
          (Scheme.Modules.pullbackCongr hb).hom.app M ≫
          (Scheme.Modules.pullback π').map e ≫
          (Scheme.Modules.pullbackCongr hk').inv.app M' ≫
          (Scheme.Modules.pullbackComp k' q).inv.app M' ≫
          (Scheme.Modules.pullback k').map t' := by
  have h := tautologicalBaseChange_general_iso b k k' hh Q q (𝟙 B) π π' hk hk' hbk hhQ
    (hb.trans (Category.comp_id _).symm) ((Scheme.Modules.pullbackId B).hom.app M ≫ e) t t' sym
    src hsrc hsym
  refine ⟨(Scheme.Modules.pullbackComp b k).app T ≪≫ (Scheme.Modules.pullbackCongr hbk).app T ≪≫
    ((Scheme.Modules.pullbackComp k' hh).app T).symm ≪≫ (Scheme.Modules.pullback k').mapIso sym,
    ?_⟩
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
  rw [h, reassoc_of% (pullbackCongr_comp_pullbackComp_id_inv
    (hb.trans (Category.comp_id _).symm) hb M M' e)]

end General

variable {X : Scheme.{u}} {G Q : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} Q] (g : G ⟶ Q) [Epi g]

/-- The closed immersion `𝐏(𝒬) ⟶ 𝐏(𝒢)` of the `SheafGradedAlgebra` presentation, at arbitrary
witnesses of the quasi-coherence of the homogeneous pieces. -/
def embeddingOfPieces (hG : Stacks.SymGraded.IsQuasicoherentPieces G)
    (hQ : Stacks.SymGraded.IsQuasicoherentPieces Q) :
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
        (Stacks.SymGraded.schemeSheafGradedAlgebra Q hQ)).scheme ⟶
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
        (Stacks.SymGraded.schemeSheafGradedAlgebra G hG)).scheme :=
  Stacks.AlgebraicGeometry.ProjBundleSurjection.map
    (Stacks.Chow.GenuineChern.surjectiveOnAffineSections_schemeSheafGradedAlgebraHom g hG hQ)

/-- The closed immersion `embeddingOfPieces g hG hQ` lies over `X`. -/
theorem embeddingOfPieces_comp_toBase (hG : Stacks.SymGraded.IsQuasicoherentPieces G)
    (hQ : Stacks.SymGraded.IsQuasicoherentPieces Q) :
    embeddingOfPieces g hG hQ ≫ (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
        (Stacks.SymGraded.schemeSheafGradedAlgebra G hG)).toBase =
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
        (Stacks.SymGraded.schemeSheafGradedAlgebra Q hQ)).toBase ≫ 𝟙 X :=
  (Stacks.AlgebraicGeometry.ProjBundleSurjection.map_comp_toBase _).trans
    (Category.comp_id _).symm

omit [Epi g] [SheafOfModules.IsFiniteLocallyFree G] [SheafOfModules.IsFiniteLocallyFree Q] in
private theorem homEquiv_comp_apply_aux (U : X.Opens) (x : Γ(G, U)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv G Q
        ((Scheme.Modules.pullbackId X).hom.app G ≫ g)).val.app (op U) x = g.val.app (op U) x :=
  Stacks.Chow.GenuineChern.homEquiv_pullbackId_comp_apply g U x

/-- On affine charts, `embeddingOfPieces g hG hQ` is induced by a graded ring map sending each
degree-one generator `x` of the symmetric algebra of `G` to the generator `g x` of that of `Q`. -/
theorem embeddingOfPieces_chart (hG : Stacks.SymGraded.IsQuasicoherentPieces G)
    (hQ : Stacks.SymGraded.IsQuasicoherentPieces Q) (x' : X) :
    ∃ (U' : X.Opens) (hU' : IsAffineOpen U') (_ : x' ∈ U') (U : X.Opens) (hU : IsAffineOpen U)
      (hUU' : U' ≤ (𝟙 X) ⁻¹ᵁ U)
      (φ : (Stacks.SymGraded.schemeSheafGradedAlgebra G hG).grading U →+*ᵍ
        (Stacks.SymGraded.schemeSheafGradedAlgebra Q hQ).grading U')
      (hφ : HomogeneousIdeal.irrelevant
          ((Stacks.SymGraded.schemeSheafGradedAlgebra Q hQ).grading U')
        ≤ (HomogeneousIdeal.irrelevant
          ((Stacks.SymGraded.schemeSheafGradedAlgebra G hG).grading U)).map φ),
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
          (Stacks.SymGraded.schemeSheafGradedAlgebra Q hQ)).chart U' hU' ≫
          embeddingOfPieces g hG hQ =
        AlgebraicGeometry.Proj.map φ hφ ≫
          (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
            (Stacks.SymGraded.schemeSheafGradedAlgebra G hG)).chart U hU ∧
      ∀ x : Γ(G, U),
        φ (DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra G hG).sectionPieces U) 1
            ((Scheme.Modules.symmetricAlgebraGen X G).val.app (op U) x)) =
          DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra Q hQ).sectionPieces U') 1
            ((Scheme.Modules.symmetricAlgebraGen X Q).val.app (op U')
              (Q.val.map (homOfLE hUU').op
                (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv G Q
                  ((Scheme.Modules.pullbackId X).hom.app G ≫ g)).val.app (op U) x))) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := x') (U := ⊤) trivial
  refine ⟨U, hU, hxU, U, hU, le_rfl,
    (Stacks.SymGraded.schemeSheafGradedAlgebraHom g hG hQ).sectionHom U,
    Stacks.AlgebraicGeometry.ProjBundleSurjection.irrelevant_le_map_sectionHom
      (Stacks.Chow.GenuineChern.surjectiveOnAffineSections_schemeSheafGradedAlgebraHom g hG hQ) hU,
    ?_, fun x => ?_⟩
  · refine (Stacks.AlgebraicGeometry.ProjBundleSurjection.chart_comp_map _ U hU).trans ?_
    rw [Stacks.AlgebraicGeometry.ProjBundleSurjection.chartMap_eq_map]
  · refine (Stacks.Chow.GenuineChern.sectionHom_of_symmetricAlgebraGen g hG hQ U x).trans ?_
    refine congrArg (fun z => DirectSum.of
      ((Stacks.SymGraded.schemeSheafGradedAlgebra Q hQ).sectionPieces U) 1
        ((Scheme.Modules.symmetricAlgebraGen X Q).val.app (op U) z)) ?_
    refine Eq.trans ?_ (congrArg (Q.val.map (homOfLE (le_rfl : U ≤ (𝟙 X) ⁻¹ᵁ U)).op)
      (homEquiv_comp_apply_aux g U x)).symm
    show _ = Q.presheaf.map (𝟙 (op U)) _
    rw [CategoryTheory.Functor.map_id]
    rfl

/-- **The twist of `𝐏(𝒢)` pulls back to the twist of `𝐏(𝒬)`** compatibly with the tautological
quotients, at arbitrary witnesses of quasi-coherence. -/
theorem exists_embeddingOfPieces_twistIso (hG : Stacks.SymGraded.IsQuasicoherentPieces G)
    (hQ : Stacks.SymGraded.IsQuasicoherentPieces Q) :
    ∃ τ : (Scheme.Modules.pullback (embeddingOfPieces g hG hQ)).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist G hG) ≅
        Stacks.ProjectiveBundleSplitting.tautologicalTwist Q hQ,
      Stacks.Chow.GenuineChern.twistQuotientPullback (𝟙 X) hG hQ (embeddingOfPieces g hG hQ)
          (embeddingOfPieces_comp_toBase g hG hQ) ≫ τ.hom =
        Stacks.Chow.GenuineChern.twistQuotientTarget (𝟙 X) hQ
          ((Scheme.Modules.pullbackId X).hom.app G ≫ g) :=
  (Stacks.Chow.GenuineChern.existsUnique_twistIso (𝟙 X) hG hQ
    ((Scheme.Modules.pullbackId X).hom.app G ≫ g) (embeddingOfPieces g hG hQ)
    (embeddingOfPieces_comp_toBase g hG hQ) (embeddingOfPieces_chart g hG hQ)).exists

variable [G.IsQuasicoherent] [Q.IsQuasicoherent]

/-- The closed immersion `𝐏(𝒬) ⟶ 𝐏(𝒢)` between the `SheafGradedAlgebra` presentations compared
with `Stacks.RelativeProj.projectiveBundle` by `Stacks.RelativeProj.bundlePresentationIso`. -/
@[irreducible] def embeddingCore :
    (Stacks.RelativeProj.symGradedBundle Q).scheme ⟶
      (Stacks.RelativeProj.symGradedBundle G).scheme :=
  embeddingOfPieces g (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G)
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent Q)

/-- The closed immersion `embeddingCore g` lies over `X`. -/
theorem embeddingCore_comp_toBase :
    embeddingCore g ≫ (Stacks.RelativeProj.symGradedBundle G).toBase =
      (Stacks.RelativeProj.symGradedBundle Q).toBase ≫ 𝟙 X := by
  unfold embeddingCore
  exact embeddingOfPieces_comp_toBase g _ _

/-- On affine charts, `embeddingCore g` is induced by a graded ring map sending each degree-one
generator `x` of the symmetric algebra of `G` to the generator `g x` of that of `Q`. -/
theorem embeddingCore_chart (x' : X) :
    ∃ (U' : X.Opens) (hU' : IsAffineOpen U') (_ : x' ∈ U') (U : X.Opens) (hU : IsAffineOpen U)
      (hUU' : U' ≤ (𝟙 X) ⁻¹ᵁ U)
      (φ : (Stacks.SymGraded.schemeSheafGradedAlgebra G
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G)).grading U →+*ᵍ
        (Stacks.SymGraded.schemeSheafGradedAlgebra Q
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent Q)).grading U')
      (hφ : HomogeneousIdeal.irrelevant ((Stacks.SymGraded.schemeSheafGradedAlgebra Q
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent Q)).grading U') ≤
        (HomogeneousIdeal.irrelevant ((Stacks.SymGraded.schemeSheafGradedAlgebra G
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G)).grading U)).map φ),
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
          (Stacks.SymGraded.schemeSheafGradedAlgebra Q
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent Q))).chart U' hU' ≫
          embeddingCore g =
        AlgebraicGeometry.Proj.map φ hφ ≫
          (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
            (Stacks.SymGraded.schemeSheafGradedAlgebra G
              (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G))).chart U hU ∧
      ∀ x : Γ(G, U),
        φ (DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra G
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G)).sectionPieces U) 1
            ((Scheme.Modules.symmetricAlgebraGen X G).val.app (op U) x)) =
          DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra Q
              (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent Q)).sectionPieces U') 1
            ((Scheme.Modules.symmetricAlgebraGen X Q).val.app (op U')
              (Q.val.map (homOfLE hUU').op
                (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv G Q
                  ((Scheme.Modules.pullbackId X).hom.app G ≫ g)).val.app (op U) x))) := by
  unfold embeddingCore
  exact embeddingOfPieces_chart g _ _ x'

/-- **The closed immersion `𝐏(𝒬) ⟶ 𝐏(𝒢)` of `Stacks.RelativeProj.projectiveBundle`.** -/
abbrev situationEmbedding :
    Stacks.RelativeProj.projectiveBundle X Q ⟶ Stacks.RelativeProj.projectiveBundle X G :=
  (Stacks.RelativeProj.bundlePresentationIso Q).inv ≫
    embeddingCore g ≫
    (Stacks.RelativeProj.bundlePresentationIso G).hom

/-- It is the embedding through `Stacks.Chow.GenuineChern.bundleEmbedding`. -/
theorem situationEmbedding_eq :
    situationEmbedding g = (Stacks.RelativeProj.bundlePresentationIso Q).inv ≫
      Stacks.Chow.GenuineChern.bundleEmbedding g ≫
        (Stacks.RelativeProj.bundlePresentationIso G).hom := by
  unfold situationEmbedding embeddingCore
  rfl

/-- `situationEmbedding g` followed by the inverse comparison isomorphism of `𝐏(𝒢)` is the inverse
comparison isomorphism of `𝐏(𝒬)` followed by `embeddingCore g`. -/
theorem situationEmbedding_comp_bundlePresentationIso_inv :
    situationEmbedding g ≫ (Stacks.RelativeProj.bundlePresentationIso G).inv =
      (Stacks.RelativeProj.bundlePresentationIso Q).inv ≫
        embeddingCore g :=
  (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Stacks.RelativeProj.bundlePresentationIso G).hom_inv_id).trans
      (Category.comp_id _))))

/-- The closed immersion `situationEmbedding g` lies over `X`, as `ι ≫ π_𝒢 = π_𝒬 ≫ 𝟙 X`. -/
theorem situationEmbedding_comp_toBase :
    situationEmbedding g ≫ Stacks.RelativeProj.projectiveBundleToBase X G =
      Stacks.RelativeProj.projectiveBundleToBase X Q ≫ 𝟙 X :=
  ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Stacks.RelativeProj.bundlePresentationIso_hom_comp_toBase G))))).trans
    ((congrArg (_ ≫ ·) ((embeddingCore_comp_toBase g).trans (Category.comp_id _))).trans
      ((Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase Q).trans
        (Category.comp_id _).symm))

/-- The comparison of the twists of the `SheafGradedAlgebra` presentation. -/
def embeddingTwistIso :
    (Scheme.Modules.pullback (embeddingCore g)).obj
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist G
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G)) ≅
      Stacks.ProjectiveBundleSplitting.tautologicalTwist Q
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent Q) :=
  Stacks.Chow.GenuineChern.twistPullbackIso (𝟙 X)
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G)
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent Q)
    ((Scheme.Modules.pullbackId X).hom.app G ≫ g) (embeddingCore g) (embeddingCore_comp_toBase g)
    (embeddingCore_chart g)

/-- The isomorphism `embeddingTwistIso g` carries the pulled-back tautological quotient of `𝒢` to
the tautological quotient of `𝒬` precomposed with `g`. -/
theorem embeddingTwistIso_spec :
    Stacks.Chow.GenuineChern.twistQuotientPullback (𝟙 X)
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G)
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent Q) (embeddingCore g)
        (embeddingCore_comp_toBase g) ≫ (embeddingTwistIso g).hom =
      Stacks.Chow.GenuineChern.twistQuotientTarget (𝟙 X)
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent Q)
        ((Scheme.Modules.pullbackId X).hom.app G ≫ g) :=
  Stacks.Chow.GenuineChern.twistQuotientPullback_comp_twistPullbackIso (𝟙 X) _ _ _ _ _ _

/-- The closed immersion lies over `X`. -/
theorem situationEmbedding_comp_toBase' :
    situationEmbedding g ≫ Stacks.RelativeProj.projectiveBundleToBase X G =
      Stacks.RelativeProj.projectiveBundleToBase X Q :=
  (situationEmbedding_comp_toBase g).trans (Category.comp_id _)


/-- **The twist of `𝐏(𝒢)` restricts to the twist of `𝐏(𝒬)`, in the presentation
`Stacks.RelativeProj.projectiveBundle`**: some isomorphism `ι^*𝒪_{𝐏(𝒢)}(1) ≅ 𝒪_{𝐏(𝒬)}(1)` carries
the pulled-back tautological quotient of `𝒢`, read on `π_𝒬^*𝒢 ≅ ι^*π_𝒢^*𝒢`, to the tautological
quotient of `𝒬` precomposed with `π_𝒬^*g`. -/
theorem exists_situationEmbedding_twistIso :
    ∃ θ : (Scheme.Modules.pullback (situationEmbedding g)).obj
        (Stacks.RelativeProj.tautologicalDatumTwist G) ≅
        Stacks.RelativeProj.tautologicalDatumTwist Q,
      (Scheme.Modules.pullback (situationEmbedding g)).map
          (Stacks.RelativeProj.tautologicalDatumUniv G) ≫ θ.hom =
        (Scheme.Modules.pullbackComp (situationEmbedding g)
            (Stacks.RelativeProj.projectiveBundleToBase X G)).hom.app G ≫
          (Scheme.Modules.pullbackCongr (situationEmbedding_comp_toBase' g)).hom.app G ≫
          (Scheme.Modules.pullback (Stacks.RelativeProj.projectiveBundleToBase X Q)).map g ≫
          Stacks.RelativeProj.tautologicalDatumUniv Q := by
  rw [Stacks.RelativeProj.tautologicalDatumUniv_eq G,
    Stacks.RelativeProj.tautologicalDatumUniv_eq Q]
  exact exists_iso_of_tautologicalBaseChange (situationEmbedding g)
    (Stacks.RelativeProj.bundlePresentationIso G).inv
    (Stacks.RelativeProj.bundlePresentationIso Q).inv
    (embeddingCore g)
    (Stacks.RelativeProj.symGradedBundle G).toBase (Stacks.RelativeProj.symGradedBundle Q).toBase
    (Stacks.RelativeProj.projectiveBundleToBase X G)
    (Stacks.RelativeProj.projectiveBundleToBase X Q)
    (Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase G)
    (Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase Q)
    (situationEmbedding_comp_bundlePresentationIso_inv g)
    (embeddingCore_comp_toBase g)
    (situationEmbedding_comp_toBase' g) g
    (Stacks.ProjectiveBundleSplitting.tautologicalMap G
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G))
    (Stacks.ProjectiveBundleSplitting.tautologicalMap Q
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent Q))
    (embeddingTwistIso g)
    (Stacks.Chow.GenuineChern.twistPullbackSourceIso (𝟙 X)
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent G)
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent Q) (embeddingCore g)
      (embeddingCore_comp_toBase g)) rfl
    (embeddingTwistIso_spec g)

/-- Transport of an identity `f₀^*u₀ ≫ θ = (f₀ ≫ π₀ ≅ π₀')-comparison ≫ w₀` to data
`(f, π, π', M, T, T', u, w)` agreeing with `(f₀, π₀, π₀', M₀, T₀, T₀', u₀, w₀)` up to heterogeneous
equality, the comparison written through `CategoryTheory.Iso.app` and its second factor replaced
by an equal morphism `c`. -/
theorem exists_iso_pullback_map_comp_eq_of_heq {P P' Y P₀ P₀' Y₀ : Scheme.{u}} (eP : P = P₀)
    (eP' : P' = P₀') (eY : Y = Y₀) {f : P' ⟶ P} {f₀ : P₀' ⟶ P₀} (ef : HEq f f₀)
    {π : P ⟶ Y} {π₀ : P₀ ⟶ Y₀} (eπ : HEq π π₀) {π' : P' ⟶ Y} {π₀' : P₀' ⟶ Y₀}
    (eπ' : HEq π' π₀') (h : f ≫ π = π') (h₀ : f₀ ≫ π₀ = π₀') {M : Y.Modules} {M₀ : Y₀.Modules}
    (eM : HEq M M₀) {T : P.Modules} {T₀ : P₀.Modules} (eT : HEq T T₀) {T' : P'.Modules}
    {T₀' : P₀'.Modules} (eT' : HEq T' T₀') {u : (Scheme.Modules.pullback π).obj M ⟶ T}
    {u₀ : (Scheme.Modules.pullback π₀).obj M₀ ⟶ T₀} (eu : HEq u u₀)
    {w : (Scheme.Modules.pullback π').obj M ⟶ T'}
    {w₀ : (Scheme.Modules.pullback π₀').obj M₀ ⟶ T₀'} (ew : HEq w w₀)
    {c : (Scheme.Modules.pullback (f ≫ π)).obj M ⟶ (Scheme.Modules.pullback π').obj M}
    (hc : c = ((Scheme.Modules.pullbackCongr h).app M).hom)
    (H : ∃ θ : (Scheme.Modules.pullback f₀).obj T₀ ≅ T₀',
      (Scheme.Modules.pullback f₀).map u₀ ≫ θ.hom =
        (Scheme.Modules.pullbackComp f₀ π₀).hom.app M₀ ≫
          (Scheme.Modules.pullbackCongr h₀).hom.app M₀ ≫ w₀) :
    ∃ θ : (Scheme.Modules.pullback f).obj T ≅ T',
      (Scheme.Modules.pullback f).map u ≫ θ.hom =
        ((Scheme.Modules.pullbackComp f π).app M).hom ≫ c ≫ w := by
  subst eP eP' eY
  obtain rfl := eq_of_heq ef
  obtain rfl := eq_of_heq eπ
  obtain rfl := eq_of_heq eπ'
  obtain rfl := eq_of_heq eM
  obtain rfl := eq_of_heq eT
  obtain rfl := eq_of_heq eT'
  obtain rfl := eq_of_heq eu
  obtain rfl := eq_of_heq ew
  subst hc
  simpa only [Iso.app_hom] using H

end AlgebraicGeometry.Space.PrivateChern

end
