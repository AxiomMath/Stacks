module

public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.AlgClosureFGSubalgebraDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent
import all StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent

/-!
# Scheme models of algebraic spaces over a field after a base change

Two consequences of Stacks 07SR and 09NS for an algebraic space `X` over a field `k`, used in
the descent arguments of Chapter 72 (Spaces over Fields).

* If `X` is quasi-compact and quasi-separated and `X_K` is a scheme for a field extension `K/k`,
  then `X_A` is a scheme for some finitely generated `k`-subalgebra `A` of `K`: `X_K` is the
  limit of the `X_A`, so this is Stacks 07SR.
* If `k` is finite, `X` is quasi-compact and quasi-separated and `X_A` is a scheme for a
  `k`-algebra `A`, then
  `X` is affine over an algebraic space `G` of finite presentation over `k` with `G_A` a scheme:
  by Stacks 09NS `X` is the limit of algebraic spaces of finite presentation over `k` with affine
  transition morphisms, and by Stacks 07SR applied to their base changes to `A` one of them has
  `G_A` a scheme. The approximation exists on an enlargement of the big fppf site, where `X` has a
  small atlas, so `G` lives there; representability of `G` transports back to `X`.

## Main results

* `AlgebraicGeometry.Space.exists_fg_isRepresentable_baseChange_subalgebra`
* `AlgebraicGeometry.Space.exists_finitePresentation_model_of_isRepresentable_baseChange_affine`

## References

* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 09NS](https://stacks.math.columbia.edu/tag/09NS)
* [Stacks Project, Tag 0B85](https://stacks.math.columbia.edu/tag/0B85)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **A scheme after a field extension is a scheme after a finitely generated subalgebra.** For a
quasi-compact quasi-separated algebraic space `X` over a field `k` and a field extension `K/k`
with `X_K` a scheme, there is a finitely generated `k`-subalgebra `A` of `K` with `X_A` a scheme
(Stacks 07SR for the system of the `X_A`). -/
theorem exists_fg_isRepresentable_baseChange_subalgebra
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hXqc : IsQuasiCompactSpace B (Spec (.of k)) hk X)
    (hXqs : IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal X)
    (hXK : ((OverShriek.relocalizeRestrict (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) : B.obj hK ⟶ B.obj hk)).obj
        X).IsRepresentable) :
    ∃ (A : Subalgebra k K) (_ : A.FG) (hA : B.Contains (Spec (.of A))),
      ((OverShriek.relocalizeRestrict (ObjectProperty.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) : B.obj hA ⟶ B.obj hk)).obj
          X).IsRepresentable := by
  obtain ⟨A, hA⟩ := exists_fgSubalgebra_isRepresentable_relocalizeRestrict k K B hk hK X hX hXqc
    hXqs hXK
  exact ⟨A.1, A.2, contains_spec_subalgebra k K B hK A.1, hA⟩

/-- **A finite-presentation model of an algebraic space with a scheme base change.** Let `F` be a
quasi-compact quasi-separated algebraic space over a finite field `k` and `A` a `k`-algebra with
`F_A` a scheme. On an enlargement `B'` of the big fppf site there is an algebraic space `G` of
finite presentation over `k` with `G_A` a scheme and such that `F` is a scheme as soon as `G` is
(`F` is affine over `G`). This combines Stacks 09NS, for the approximation of `F` by spaces of
finite presentation over `k` with affine transition morphisms, and Stacks 07SR, for one of them
with a scheme base change to `A`. -/
theorem exists_finitePresentation_model_of_isRepresentable_baseChange_affine
    (k : Type u) [Field k] [Finite k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (F : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B (Spec (.of k)) hk F)
    (hFqc : IsQuasiCompactSpace B (Spec (.of k)) hk F)
    (hFqs : IsAbsolutelyQuasiSeparated B (Spec (.of k)) hk B.contains_terminal F)
    (A : Type u) [CommRing A] [Algebra k A] (hA : B.Contains (Spec (.of A)))
    (hbase : ((OverShriek.relocalizeRestrict (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) : B.obj hA ⟶ B.obj hk)).obj
        F).IsRepresentable) :
    ∃ (B' : BigFppfSite.{u}), IsContained (τ := .fppf) B B' ∧
      ∃ (hk' : B'.Contains (Spec (.of k))) (hA' : B'.Contains (Spec (.of A)))
      (G : (BigFppfOver B' (Spec (.of k)) hk')ᵒᵖ ⥤ Type u),
      IsAlgebraicSpace B' (Spec (.of k)) hk' G ∧
      ∃ (f : G ⟶ yoneda.obj (Over.mk (𝟙 (B'.obj hk')))),
      IsFinitePresentation B' (Spec (.of k)) hk' f ∧
      ((OverShriek.relocalizeRestrict (ObjectProperty.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) : B'.obj hA' ⟶ B'.obj hk')).obj
          G).IsRepresentable ∧
      (G.IsRepresentable → F.IsRepresentable) := by
  obtain ⟨B', h, hcof⟩ := BigFppfSite.exists_isContained_lt_cof B B.cutoff
  let hk' : B'.Contains (Spec (.of k)) := largerContains h hk
  let hA' : B'.Contains (Spec (.of A)) := largerContains h hA
  let X : AlgebraicSpaces B (Spec (.of k)) hk := ⟨F, hF⟩
  let X' := (changeBigSite B B' h (Spec (.of k)) hk).obj X
  have hX'qc := changeBigSite_isQuasiCompactSpace B B' h _ hk X hFqc
  have hX'qs := changeBigSite_isAbsolutelyQuasiSeparated B B' h _ hk X hFqc hFqs
  -- `F_A` is a scheme on the enlarged site
  let φ : B.obj hA ⟶ B.obj hk :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  let T : BigFppfOver B (Spec (.of k)) hk := Over.mk φ
  have hFT : IsAlgebraicSpace B (Spec (.of k)) hk (F ⨯ yoneda.obj T) :=
    isAlgebraicSpace_prod B (Spec (.of k)) hk hF (isAlgebraicSpace_yoneda B (Spec (.of k)) hk T)
  have h2 := (isRepresentable_prod_yoneda_iff_changeBigSite B B' h _ hk X T hFT).2
    (PurelyTranscendentalDescent.isRepresentable_prod_of_relocalizeRestrict φ F hbase)
  let φ' : B'.obj hA' ⟶ B'.obj hk' :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  have h3 : ((OverShriek.relocalizeRestrict φ').obj X'.obj).IsRepresentable :=
    PurelyTranscendentalDescent.isRepresentable_relocalizeRestrict_of_prod φ' X'.obj h2
  -- the small approximation of `X'` by spaces of finite presentation over `k` (Stacks 09NS)
  have := locallyOfFiniteType_terminal_from_spec_of_finiteType k
  have hSfp := locallyOfFinitePresentation_terminal_from (Spec (.of k))
  let hZ' : B'.Contains (⊤_ Scheme.{u}) := B'.contains_terminal
  let g' : B'.obj hk' ⟶ B'.obj hZ' := ⟨terminal.from _⟩
  have hXZalg := isAlgebraicSpace_viewOver B' (Spec (.of k)) (⊤_ Scheme.{u}) hk' hZ' g' X'.obj
    X'.property
  have hXZqc := isQuasiCompactSpace_relocalize B' (Spec (.of k)) hk' hZ' g' hX'qc
  have hXZqs := isAbsolutelyQuasiSeparated_viewOverIntegers B' (Spec (.of k)) hk' hZ' X'.obj hX'qs
  obtain ⟨U, q, -, hqs, hqe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B (Spec (.of k)) hk F hF).1 hFqc
  obtain ⟨R, s, t, q', hq's, hq'e, -, -⟩ := changeBigSite_atlas B B' h _ hk X q hqs
    ((isEtale_iff_presheaf_of_yoneda B _ hk q).1 hqe)
  have hsmall : HasSmallNoetherianApproximation B' (⊤_ Scheme.{u}) hZ' hZ'
      (viewOverIntegers B' (Spec (.of k)) hk' hZ' X'.obj) :=
    hasSmallNoetherianApproximation_of_etaleAtlas hXZalg hXZqc hXZqs _
      (relocalizeChart B' (Spec (.of k)) (⊤_ Scheme.{u}) hk' hZ' g' q')
      ((presheaf_relocalizeChart_iff B' (Spec (.of k)) (⊤_ Scheme.{u}) hk' hZ' g' _ q').2 hq's)
      ((isEtale_iff_presheaf_of_yoneda B' _ hZ' _).mpr
        ((presheaf_relocalizeChart_iff B' (Spec (.of k)) (⊤_ Scheme.{u}) hk' hZ' g' _ q').2 hq'e))
      (lt_trans U.left.property hcof)
  obtain ⟨I, _, _, _, hI, D, p, ⟨hp⟩, hD, hfp, haff⟩ :=
    exists_finitePresentation_system_of_hasSmallNoetherianApproximation B' (Spec (.of k)) hk' hSfp
      X'.property hsmall
  have hfp' : ∀ i, IsFinitePresentation B' (Spec (.of k)) hk'
      ((IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal).from (D.obj i)) := fun i => by
    rw [(IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal).hom_ext
      ((IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal).from (D.obj i))
      (toYonedaId B' (Spec (.of k)) hk' (D.obj i))]
    exact hfp i
  -- a stage with a scheme base change to `A` (Stacks 07SR)
  obtain ⟨G, hG, f, gG, hfpG, hg, hGbase⟩ :=
    PurelyTranscendentalDescent.exists_finitePresentation_model_of_isRepresentable_baseChange k B'
      hk' X'.obj X'.property (Over.mk φ')
      (inferInstanceAs (_root_.AlgebraicGeometry.IsAffineHom
        (Spec.map (CommRingCat.ofHom (algebraMap k A))))) h3 hI D p hp hD hfp' haff
  refine ⟨B', h, hk', hA', G, hG, f, hfpG, hGbase, fun hGrep => ?_⟩
  have hrel := ((isAffineHom_tfae_of_isAlgebraicSpace B' (Spec (.of k)) hk' gG X'.property hG).out
    2 1).mp hg
  exact isRepresentable_of_isRepresentable_changeBigSite B B' h _ hk X
    (PurelyTranscendentalDescent.isRepresentable_of_relativelyRepresentable_of_isRepresentable gG
      hrel.1 hGrep)

end AlgebraicGeometry.Space

end
