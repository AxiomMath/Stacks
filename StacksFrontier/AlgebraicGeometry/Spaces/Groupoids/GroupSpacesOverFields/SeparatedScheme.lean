module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpacesOverFields.JacobsonBaseChangeScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpacesOverFields.AlgebraicClosureScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Extension
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactDiagonalQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.AlgClosureSchemeDescent
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrictProduct

/-!
# A separated group algebraic space over a field is a scheme

Stacks 0B8G: let `k` be a field and `G` a group algebraic space over `k`. If `G` is separated,
then `G` is a scheme. Here `G` is a group object over the terminal presheaf of the big fppf site
of `Spec k` whose underlying presheaf is an algebraic space, and being a scheme is
representability of that presheaf.

## Main results

* `AlgebraicGeometry.Space.GroupOverField.isRepresentable_of_isSeparatedOver`: **Stacks 0B8G.**
* `AlgebraicGeometry.Space.GroupOverField.isRepresentable_of_relocalizeRestrict_algebraicClosure`:
  the core statement of
  `AlgebraicGeometry.Space.GroupOverField.isRepresentable_of_jacobsonSpace_algebraicClosure`,
  with the base change to the algebraic closure given by a representing object of the
  restriction.
* `AlgebraicGeometry.Space.GroupOverField.exists_representation_algebraicClosure`: Stacks 0479
  for the base change of `G_{k̄}` to the algebraic closure of a large extension of `k`.

## Implementation notes

The proof follows the source. By Stacks 0B8E the base change `G_{k̄}` is a scheme `X₀`. Let
`K = k(x_σ)` be purely transcendental of cardinality above the size of `X₀`; by Stacks 0B85 it
suffices that `G_K` is a scheme. With `Ω` the algebraic closure of `K` and an embedding
`k̄ → Ω`, the base change `G_Ω` is `X₀ ×_{k̄} Ω`, a Jacobson scheme all of whose closed points
are `Ω`-rational (Stacks 0479). The rest is
`AlgebraicGeometry.Space.GroupOverField.isRepresentable_of_jacobsonSpace_algebraicClosure`,
whose implementation notes describe the two places where the argument departs from the
source's: the perfect closure of `K` only enters through the algebra `Ω ⊗_F Ω`, which removes
the need for Stacks 0B83, and Stacks 0BA1 for a finite extension replaces Stacks 0B86 and
0B87.

## References

* [Stacks Project, Tag 0B8G](https://stacks.math.columbia.edu/tag/0B8G)
* [Stacks Project, Tag 0B8E](https://stacks.math.columbia.edu/tag/0B8E)
* [Stacks Project, Tag 0B85](https://stacks.math.columbia.edu/tag/0B85)
* [Stacks Project, Tag 0B84](https://stacks.math.columbia.edu/tag/0B84)
* [Stacks Project, Tag 0479](https://stacks.math.columbia.edu/tag/0479)
* [Stacks Project, Tag 0B7U](https://stacks.math.columbia.edu/tag/0B7U)
* [Stacks Project, Tag 0BA1](https://stacks.math.columbia.edu/tag/0BA1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space.GroupOverField

attribute [local instance] Over.cartesianMonoidalCategory

variable (K : Type u) [Field K] (C : BigFppfSite.{u}) (hK : C.Contains (Spec (.of K)))

/-- **A rational section through a closed point with algebraic residue field, for any structure
morphism over `K`.** Let `Ω/K` be algebraic with `Ω` algebraically closed, and let `s, t` be two
morphisms `X ⟶ Spec Ω` over `Spec K`. If the residue field of `x` is algebraic over `Ω` through
`s`, then there is a section of `t` through `x`: a section of `s` through `x`, composed with `t`,
is `Spec` of a `K`-endomorphism of `Ω`, which is an automorphism. -/
theorem exists_section_of_isAlgebraicResidue (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω] (X : Scheme.{u}) (s t : X ⟶ Spec (.of Ω))
    (hst : s ≫ Spec.map (CommRingCat.ofHom (algebraMap K Ω)) =
      t ≫ Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (x : X)
    (hx : Stacks.AlgebraicGeometry.ClosedPointResidue.IsAlgebraicResidue s x) :
    ∃ a : Spec (.of Ω) ⟶ X, a ≫ t = 𝟙 _ ∧ a (⊥ : PrimeSpectrum Ω) = x := by
  obtain ⟨σ, hσ, hσx⟩ := exists_section_of_isAlgebraic_residueField Ω X s x hx
  let τ : Spec (.of Ω) ⟶ Spec (.of Ω) := σ ≫ t
  let ψ₀ : CommRingCat.of Ω ⟶ CommRingCat.of Ω := Spec.preimage τ
  have hψ₀ : Spec.map ψ₀ = τ := Spec.map_preimage _
  have hK' : CommRingCat.ofHom (algebraMap K Ω) ≫ ψ₀ = CommRingCat.ofHom (algebraMap K Ω) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ₀]
    change (σ ≫ t) ≫ _ = _
    rw [Category.assoc, ← hst, ← Category.assoc, hσ, Category.id_comp]
  let ψ : Ω →ₐ[K] Ω := ⟨ψ₀.hom, fun c => congrArg (fun g => g.hom c) hK'⟩
  have : IsIso ψ₀ := (ConcreteCategory.isIso_iff_bijective ψ₀).2
    (Algebra.IsAlgebraic.algHom_bijective ψ)
  have : IsIso τ := by
    rw [← hψ₀]
    infer_instance
  exact ⟨inv τ ≫ σ, by simp [τ], hσx _⟩

/-- **The core, with the geometric base change given in the restriction spelling.** Let `P` be a
quasi-separated group algebraic space over a field `K`, and let `W` represent its base change
to the algebraic closure `Ω` of `K` (restriction along `Spec Ω ⟶ Spec K`). If the scheme of `W`
is Jacobson and its closed points have residue fields algebraic over `Ω`, then `P` is a scheme.

The base change in the product spelling `h_Ω × P` is represented by `W` viewed over `Spec K`
(Stacks 03I4 and 04SH), and every closed point is a rational section for its structure morphism
by `AlgebraicGeometry.Space.GroupOverField.exists_section_of_isAlgebraicResidue`; so
`AlgebraicGeometry.Space.GroupOverField.isRepresentable_of_jacobsonSpace_algebraicClosure`
applies. -/
theorem isRepresentable_of_relocalizeRestrict_algebraicClosure
    (P : Grp ((BigFppfOver C (Spec (.of K)) hK)ᵒᵖ ⥤ Type u))
    (hP : IsAlgebraicSpace C _ hK P.X)
    (W : BigFppfOver C (Spec (.of (AlgebraicClosure K)))
      (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK))
    (eW : yoneda.obj W ≅ (OverShriek.relocalizeRestrict (specExtensionHom K (AlgebraicClosure K) C
      hK (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK))).obj P.X)
    (hJW : JacobsonSpace ((BigFppfOver.toScheme C _ _).obj W))
    (hratW : ∀ x : (BigFppfOver.toScheme C _ _).obj W, IsClosed ({x} : Set _) →
      Stacks.AlgebraicGeometry.ClosedPointResidue.IsAlgebraicResidue W.hom.hom x)
    (hPqs : IsQuasiSeparatedOver C _ hK P.X) :
    P.X.IsRepresentable := by
  let Ω := AlgebraicClosure K
  let hΩ : C.Contains (Spec (.of Ω)) := contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK
  let f := specExtensionHom K Ω C hK hΩ
  let EΩ := extObj C (Spec (.of K)) hK (Iso.refl _) Ω hΩ
  have hE : Over.mk f = EΩ := over_mk_specExtensionHom_eq_extObj K C hK Ω hΩ
  let Z : BigFppfOver C (Spec (.of K)) hK := (Over.map f).obj W
  let eZ : yoneda.obj Z ≅ yoneda.obj EΩ ⨯ P.X :=
    (relocalizedYonedaIso C (C.obj hΩ) (C.obj hK) f W).symm ≪≫
      (OverShriek.relocalizePresheafFunctor f).mapIso eW ≪≫
        OverShriek.relocalizeRestrictIsoProduct f P.X ≪≫
          prod.mapIso (eqToIso (congrArg yoneda.obj hE)) (Iso.refl _)
  let Y : Over EΩ := Over.mk (yoneda.preimage (eZ.hom ≫ prod.fst))
  let eY : (Over.post yoneda).obj Y ≅ Over.mk (prod.fst : yoneda.obj EΩ ⨯ P.X ⟶ _) :=
    Over.isoMk eZ (Functor.map_preimage yoneda _).symm
  refine isRepresentable_of_jacobsonSpace_algebraicClosure K C hK P hP Y eY hJW
    (fun x hx => ?_) hPqs
  have hst : W.hom.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Ω)) =
      (BigFppfOver.toScheme C _ hK).map Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
    have h := congrArg (fun g => g.hom) (Over.w Y.hom)
    simp only [EΩ] at h
    change _ = Y.hom.left.hom ≫ _
    rw [← Category.comp_id (Spec.map _), ← Iso.refl_inv, ← Category.assoc, ← Category.assoc]
    exact h.symm
  obtain ⟨a, ha, hax⟩ := exists_section_of_isAlgebraicResidue K Ω _ W.hom.hom
    ((BigFppfOver.toScheme C _ hK).map Y.hom) hst x (hratW x hx)
  exact ⟨Over.homMk a ha, hax⟩

/-- **A large purely transcendental extension inside the site.** For every cardinal `κ` below the
cutoff of a big fppf site containing `Spec k`, some field of rational functions over `k` has
cardinality above `κ` and spectrum in the site: take `Order.succ (max κ (max #k ℵ₀))` variables,
a cardinal still below the cutoff, which is a strong limit. -/
theorem exists_mvRatFunc_contains_lt (k : Type u) [Field k] (hk : C.Contains (Spec (.of k)))
    (κ : Cardinal.{u}) (hκ : κ < C.cutoff) :
    ∃ σ : Type u, C.Contains (Spec (.of (MvRatFunc σ k))) ∧ κ < Cardinal.mk (MvRatFunc σ k) := by
  classical
  have hkcard : Cardinal.mk k < C.cutoff := by
    have h : (Spec (CommRingCat.of k)).size < C.cutoff := hk
    rw [AlgebraicGeometry.Scheme.size_Spec] at h
    exact (le_max_right _ _).trans_lt h
  let bound : Cardinal.{u} := max κ (max (Cardinal.mk k) Cardinal.aleph0)
  let κplus : Cardinal.{u} := Order.succ bound
  have hkbound : Cardinal.mk k ≤ bound := (le_max_left _ _).trans (le_max_right _ _)
  have hwbound : Cardinal.aleph0 ≤ bound := (le_max_right _ _).trans (le_max_right _ _)
  have hsucclt : κplus < C.cutoff := C.cutoff_isStrongPrelimit.isSuccPrelimit.succ_lt
    (max_lt hκ (max_lt hkcard C.aleph0_lt_cutoff))
  let σ : Type u := Quotient.out κplus
  have hσ : Cardinal.mk σ = κplus := Cardinal.mk_out κplus
  have : Nonempty σ := by
    rw [← Cardinal.mk_ne_zero_iff, hσ]
    exact (Cardinal.aleph0_pos.trans_le (hwbound.trans (Order.le_succ bound))).ne'
  have hcard : Cardinal.mk (MvRatFunc σ k) = κplus := by
    have h₁ : Cardinal.mk (MvRatFunc σ k) =
        max (max (Cardinal.mk k) (Cardinal.mk σ)) Cardinal.aleph0 := by
      change Cardinal.mk (FractionRing (MvPolynomial σ k)) = _
      rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max_lift]
      simp only [Cardinal.lift_id]
    rw [h₁, hσ, max_eq_right (hkbound.trans (Order.le_succ bound)),
      max_eq_left (hwbound.trans (Order.le_succ bound))]
  refine ⟨σ, ?_, ?_⟩
  · change (Spec (CommRingCat.of (MvRatFunc σ k))).size < C.cutoff
    rw [AlgebraicGeometry.Scheme.size_Spec, hcard]
    exact max_lt C.aleph0_lt_cutoff hsucclt
  · rw [hcard]
    exact (le_max_left _ _).trans_lt (Order.lt_succ bound)

/-- **Transporting a scheme structure from an algebraic extension to a large algebraically closed
field.** Let `F` be a presheaf on the big fppf site of `Spec k` whose base change to an algebraic
extension `L/k` is represented by `Y₀`. For an extension `K/k` larger than the scheme of `Y₀`,
the base change of `F_K` to the algebraic closure `Ω` of `K` is represented by the base change
`Y₀ ×_L Ω` along an embedding `L → Ω`, a Jacobson scheme all of whose closed points have residue
fields algebraic over `Ω` (Stacks 0479). -/
theorem exists_representation_algebraicClosure (k : Type u) [Field k]
    (hk : C.Contains (Spec (.of k))) (F : (BigFppfOver C (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (L : Type u) [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (hL : C.Contains (Spec (.of L))) (Y₀ : BigFppfOver C (Spec (.of L)) hL)
    (r₀ : yoneda.obj Y₀ ≅ (OverShriek.relocalizeRestrict (specExtensionHom k L C hk hL)).obj F)
    [Algebra k K]
    (hsize : ((BigFppfOver.toScheme C _ hL).obj Y₀).size < Cardinal.mk K) :
    ∃ W : BigFppfOver C (Spec (.of (AlgebraicClosure K)))
        (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK),
      Nonempty (yoneda.obj W ≅ (OverShriek.relocalizeRestrict (specExtensionHom K
        (AlgebraicClosure K) C hK (contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK))).obj
          ((OverShriek.relocalizeRestrict (specExtensionHom k K C hk hK)).obj F)) ∧
      JacobsonSpace ((BigFppfOver.toScheme C _ _).obj W) ∧
      ∀ x : (BigFppfOver.toScheme C _ _).obj W, IsClosed ({x} : Set _) →
        Stacks.AlgebraicGeometry.ClosedPointResidue.IsAlgebraicResidue W.hom.hom x := by
  classical
  let Ω := AlgebraicClosure K
  let hΩ : C.Contains (Spec (.of Ω)) := contains_spec_of_isAlgebraic C K (AlgebraicClosure K) hK
  let ι : L →ₐ[k] Ω := IsAlgClosed.lift
  let : Algebra L Ω := ι.toRingHom.toAlgebra
  let h := specExtensionHom L Ω C hL hΩ
  have hcomm : h ≫ specExtensionHom k L C hk hL =
      specExtensionHom K Ω C hK hΩ ≫ specExtensionHom k K C hk hK := by
    apply ObjectProperty.hom_ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext c
    change ι (algebraMap k L c) = algebraMap K Ω (algebraMap k K c)
    rw [ι.commutes, ← IsScalarTower.algebraMap_apply]
  let W : BigFppfOver C (Spec (.of Ω)) hΩ := (Over.pullback h).obj Y₀
  refine ⟨W, ⟨(Over.mapPullbackAdj h).compYonedaIso.app Y₀ ≪≫
    (OverShriek.relocalizeRestrict h).mapIso r₀ ≪≫
      relocalizeRestrictCompIso h (specExtensionHom k L C hk hL) F ≪≫
        eqToIso (congrArg (fun g => (OverShriek.relocalizeRestrict g).obj F) hcomm) ≪≫
          (relocalizeRestrictCompIso (specExtensionHom K Ω C hK hΩ)
            (specExtensionHom k K C hk hK) F).symm⟩, ?_⟩
  -- the scheme of `W` is the fibre product `X₀ ×_L Ω`
  let f₀ : (BigFppfOver.toScheme C _ hL).obj Y₀ ⟶ Spec (.of L) := Y₀.hom.hom
  let e : (BigFppfOver.toScheme C _ hΩ).obj W ≅
      pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap L Ω))) :=
    PreservesPullback.iso C.inclusion Y₀.hom h
  have hK' : ((BigFppfOver.toScheme C _ hL).obj Y₀).size < Cardinal.mk Ω :=
    hsize.trans_le (Cardinal.mk_le_of_injective (algebraMap K Ω).injective)
  refine ⟨?_, fun x hx => ?_⟩
  · have := jacobsonSpace_pullback_of_size_lt L _ f₀ Ω hK'
    exact JacobsonSpace.of_isClosedEmbedding (Scheme.homeoOfIso e).isClosedEmbedding
  · have hy : e.hom x ∈ closedPoints
        (pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap L Ω))) : Scheme.{u}) := by
      simpa using (Scheme.homeoOfIso e).isClosedMap _ hx
    exact (Stacks.AlgebraicGeometry.ClosedPointResidue.isAlgebraicResidue_iff_of_comp_eq
      (pullback.snd _ _) W.hom.hom e.hom (PreservesPullback.iso_hom_snd _ _ _) x).2
      (Stacks.AlgebraicGeometry.ClosedPointResidue.isAlgebraicResidue_of_mem_closedPoints_of_size_lt
        L _ f₀ Ω hK' (e.hom x) hy)

/-- **Stacks 0B8G.** Let `k` be a field and let `G` be a group algebraic space over `k`. If `G`
is separated, then `G` is a scheme.

By Stacks 0B8E the base change `G_{k̄}` is a scheme `X₀`. For a purely transcendental extension
`K = k(x_σ)` of cardinality above the size of `X₀`, Stacks 0B85 reduces the statement to `G_K`.
With `Ω` the algebraic closure of `K`, the base change `G_Ω = X₀ ×_{k̄} Ω` is a Jacobson scheme
whose closed points are `Ω`-rational (Stacks 0479), and
`AlgebraicGeometry.Space.GroupOverField.isRepresentable_of_relocalizeRestrict_algebraicClosure`
concludes that `G_K` is a scheme. -/
@[stacks 0B8G]
theorem isRepresentable_of_isSeparatedOver {k : Type u} [Field k] (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    (G : GroupAlgebraicSpace B (Spec (.of k)) hk (yoneda.obj (⊤_ (BigFppfOver B (Spec (.of k)) hk)))
      (isAlgebraicSpace_yoneda B (Spec (.of k)) hk _))
    (hsep : IsSeparatedOver B (Spec (.of k)) hk G.obj.X.left) :
    G.obj.X.left.IsRepresentable := by
  classical
  let kbar := AlgebraicClosure k
  have hkbar : B.Contains (Spec (.of kbar)) := contains_spec_of_isAlgebraic B k kbar hk
  let := isRepresentable_relocalizeRestrict_algebraicClosure_of_isSeparatedOver B hk G hsep
  let Y₀ := ((OverShriek.relocalizeRestrict (specExtensionHom k kbar B hk hkbar)).obj
    G.obj.X.left).reprX
  obtain ⟨σ, hK, hsize⟩ := exists_mvRatFunc_contains_lt B k hk
    ((BigFppfOver.toScheme B _ hkbar).obj Y₀).size Y₀.left.property
  let K := MvRatFunc σ k
  have hGalg : IsAlgebraicSpace B _ hk G.obj.X.left := G.property
  have hGqs := isQuasiSeparatedOver_of_isSeparatedOver B _ hk _ hsep
  refine isRepresentable_of_isRepresentable_purelyTranscendental_baseChange k K B hk hK
    G.obj.X.left hGalg hGqs ?_
  let f := specExtensionHom k K B hk hK
  let P := relocalizeRestrictGrp B (Spec (.of k)) hk f (presheafGrp B _ hk G.obj)
  obtain ⟨W, ⟨eW⟩, hJW, hratW⟩ := exists_representation_algebraicClosure K B hK k hk
    G.obj.X.left kbar hkbar Y₀ (Functor.reprW _) hsize
  exact isRepresentable_of_relocalizeRestrict_algebraicClosure K B hK P
    (isAlgebraicSpace_relocalizeRestrict B _ _ hK hk f _ hGalg) W eW hJW hratW
    (isQuasiSeparatedOver_relocalizeRestrict B _ hK _ hk f _ hGqs)

end AlgebraicGeometry.Space.GroupOverField

end
